#!/usr/bin/env python3
"""
QBTC Explorer v3 (English) - blockchain explorer in a blockchain.com style
(pure Python, no external libraries).

Reads chain data from a public QBTC explorer API and serves a web page where you can search:
  - a block height (number)
  - a transaction (64 hex chars)
  - an address (qbtc1...): profile, balance, summary, transactions, balance chart, counterparties.

Run:
    python n1.py --host 0.0.0.0 --port $PORT --rpc https://explorer.qbtc-core.org

Options (all optional):
    --rpc URL        data source (default: env QBTC_RPC or https://explorer.qbtc-core.org)
    --host HOST      default 0.0.0.0
    --port PORT      default: env PORT, else 8080
    --cache FILE     index cache file (default explorer_cache.json)
    --price USD      price of one QBTC in USD (approx.)
    --delay SECONDS  pause between block requests to be gentle on the data source (default 0.02)
"""
import argparse
import json
import os
import re
import threading
import time
import urllib.request
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import urlparse, parse_qs

SATS = 100_000_000
REORG_WINDOW = 12
ZERO_TXID = "0" * 64
HRP = "qbtc"
PAGE_SIZE = 15
MAX_LIST = 60
MAX_HISTORY = 300  # max points in the balance chart
PRICE_USD = 0.001126  # price of one QBTC in USD (approx. $0.001126)

# ----------------------------------------------------------------------------
# Bech32m
# ----------------------------------------------------------------------------
_CHARSET = "qpzry9x8gf2tvdw0s3jn54khce6mua7l"
_BECH32M_CONST = 0x2BC830A3


def _polymod(values):
    gen = [0x3B6A57B2, 0x26508E6D, 0x1EA119FA, 0x3D4233DD, 0x2A1462B3]
    chk = 1
    for v in values:
        b = chk >> 25
        chk = (chk & 0x1FFFFFF) << 5 ^ v
        for i in range(5):
            chk ^= gen[i] if (b >> i) & 1 else 0
    return chk


def _hrp_expand(hrp):
    return [ord(c) >> 5 for c in hrp] + [0] + [ord(c) & 31 for c in hrp]


def decode_address(addr):
    """Returns (hrp, hash_hex) or None if the address is invalid."""
    addr = addr.strip()
    if addr != addr.lower() or "1" not in addr:
        return None
    hrp, _, data_part = addr.rpartition("1")
    if not hrp or len(data_part) < 6 or any(c not in _CHARSET for c in data_part):
        return None
    data = [_CHARSET.find(c) for c in data_part]
    if _polymod(_hrp_expand(hrp) + data) != _BECH32M_CONST:
        return None
    acc, bits, out = 0, 0, bytearray()
    for v in data[:-6]:
        acc = (acc << 5) | v
        bits += 5
        while bits >= 8:
            bits -= 8
            out.append((acc >> bits) & 0xFF)
    if len(out) < 32:
        return None
    return hrp, bytes(out[:32]).hex()


_ADDR_CACHE = {}


def encode_address(hash_hex):
    """Key hash (64 hex) -> qbtc1... address (Bech32m)."""
    got = _ADDR_CACHE.get(hash_hex)
    if got:
        return got
    raw = bytes.fromhex(hash_hex)
    acc, bits, data = 0, 0, []
    for byte in raw:
        acc = (acc << 8) | byte
        bits += 8
        while bits >= 5:
            bits -= 5
            data.append((acc >> bits) & 31)
    if bits:
        data.append((acc << (5 - bits)) & 31)
    mod = _polymod(_hrp_expand(HRP) + data + [0] * 6) ^ _BECH32M_CONST
    chk = [(mod >> 5 * (5 - i)) & 31 for i in range(6)]
    addr = HRP + "1" + "".join(_CHARSET[d] for d in data + chk)
    if len(_ADDR_CACHE) < 200000:
        _ADDR_CACHE[hash_hex] = addr
    return addr


# ----------------------------------------------------------------------------
# RPC client (read-only)
# ----------------------------------------------------------------------------
class Rpc:
    def __init__(self, base):
        self.base = base.rstrip("/")
        self.delay = 0.0

    def _call(self, path, payload=None):
        data = None if payload is None else json.dumps(payload).encode()
        req = urllib.request.Request(self.base + path, data=data)
        req.add_header("Content-Type", "application/json")
        req.add_header("User-Agent", "Mozilla/5.0 (compatible; QBTC-Explorer/3.0)")
        req.add_header("Accept", "application/json")
        with urllib.request.urlopen(req, timeout=15) as r:
            return json.loads(r.read().decode())

    def info(self):
        return self._call("/api/get_info")

    def block(self, height):
        if self.delay:
            time.sleep(self.delay)
        return self._call("/api/get_block", {"height": int(height)})

    def balance(self, address):
        return self._call("/api/get_balance", {"address": address})

    def tx_status(self, txid):
        return self._call("/api/tx_status", {"tx_hash": txid})


# ----------------------------------------------------------------------------
# Index
# ----------------------------------------------------------------------------
class Index:
    def __init__(self, rpc, cache_path):
        self.rpc = rpc
        self.cache_path = cache_path
        self.lock = threading.Lock()
        self.blocks = {}
        self.txs = {}
        self.outs = {}
        self.spent = {}
        self.addr_txs = {}
        self.tip = -1
        self.node_ok = False
        self.last_error = ""
        self._load_cache()

    def _add(self, h, blk):
        self.blocks[h] = blk
        for tx in blk.get("transactions", []):
            txid = tx["txid"]
            self.txs[txid] = (h, tx)
            touched = set()
            for i, o in enumerate(tx["outputs"]):
                self.outs[(txid, i)] = (o["value_sats"], o["address_hash"])
                touched.add(o["address_hash"])
            for inp in tx["inputs"]:
                if inp["prev_txid"] != ZERO_TXID:
                    self.spent[(inp["prev_txid"], inp["vout"])] = txid
                prev = self.outs.get((inp["prev_txid"], inp["vout"]))
                if prev:
                    touched.add(prev[1])
            for a in touched:
                self.addr_txs.setdefault(a, set()).add(txid)

    def _remove(self, h):
        blk = self.blocks.pop(h, None)
        if not blk:
            return
        for tx in blk.get("transactions", []):
            txid = tx["txid"]
            self.txs.pop(txid, None)
            for i in range(len(tx["outputs"])):
                self.outs.pop((txid, i), None)
            for inp in tx["inputs"]:
                self.spent.pop((inp["prev_txid"], inp["vout"]), None)
            for s in self.addr_txs.values():
                s.discard(txid)

    def _load_cache(self):
        try:
            with open(self.cache_path) as f:
                saved = json.load(f)
            for h, blk in sorted(saved.items(), key=lambda kv: int(kv[0])):
                self._add(int(h), blk)
            print(f"[cache] loaded {len(self.blocks)} blocks from {self.cache_path}")
        except (OSError, ValueError):
            pass

    def save_cache(self):
        with self.lock:
            snap = {str(h): b for h, b in self.blocks.items()}
        tmp = self.cache_path + ".tmp"
        with open(tmp, "w") as f:
            json.dump(snap, f, separators=(",", ":"))
        os.replace(tmp, self.cache_path)

    def run(self):
        saved_at = 0
        while True:
            try:
                tip = int(self.rpc.info()["current_height"])
                self.node_ok, self.last_error = True, ""
                with self.lock:
                    self.tip = tip
                    known = max(self.blocks) if self.blocks else -1
                start = min(known + 1, max(0, tip - REORG_WINDOW))
                start = max(0, start) if known < 0 else start
                for h in range(start, tip + 1):
                    blk = self.rpc.block(h)
                    if blk is None:
                        break
                    with self.lock:
                        self._remove(h)
                        self._add(h, blk)
                    if h - start and h % 2000 == 0 and time.time() - saved_at > 30:
                        self.save_cache()
                        saved_at = time.time()
                if time.time() - saved_at > 60:
                    self.save_cache()
                    saved_at = time.time()
            except Exception as e:
                self.node_ok, self.last_error = False, str(e)
            time.sleep(10)

    def status(self):
        with self.lock:
            return {
                "node_ok": self.node_ok,
                "error": self.last_error,
                "tip": self.tip,
                "indexed": len(self.blocks),
                "total": self.tip + 1,
            }

    def _miner(self, blk):
        try:
            cb = blk["transactions"][0]
            return encode_address(cb["outputs"][0]["address_hash"]), sum(o["value_sats"] for o in cb["outputs"])
        except (IndexError, KeyError):
            return None, 0

    def latest(self, frm, count):
        out = []
        with self.lock:
            for h in range(frm, max(frm - count, -1), -1):
                blk = self.blocks.get(h)
                if blk is None:
                    continue
                miner, reward = self._miner(blk)
                out.append({"height": h, "timestamp": blk["timestamp"],
                            "tx_count": blk["tx_count"], "miner": miner, "reward": reward})
        return out

    def _tx_info(self, txid):
        found = self.txs.get(txid)
        if not found:
            return None
        h, tx = found
        ins, total_in, known = [], 0, True
        coinbase = False
        for inp in tx["inputs"]:
            if inp["prev_txid"] == ZERO_TXID:
                coinbase = True
                ins.append({"coinbase": True, "addr": None, "value": None})
                continue
            prev = self.outs.get((inp["prev_txid"], inp["vout"]))
            if prev:
                total_in += prev[0]
                ins.append({"coinbase": False, "addr": prev[1], "value": prev[0],
                            "prev_txid": inp["prev_txid"], "vout": inp["vout"]})
            else:
                known = False
                ins.append({"coinbase": False, "addr": None, "value": None,
                            "prev_txid": inp["prev_txid"], "vout": inp["vout"]})
        outs = []
        for n, o in enumerate(tx["outputs"]):
            outs.append({"n": n, "addr": o["address_hash"], "value": o["value_sats"],
                         "spent_by": self.spent.get((txid, n))})
        total_out = sum(o["value"] for o in outs)
        fee = (total_in - total_out) if (known and not coinbase) else None
        return {"txid": txid, "height": h, "timestamp": self.blocks[h]["timestamp"],
                "confirmations": self.tip - h + 1, "inputs": ins, "outputs": outs,
                "total_in": total_in, "total_out": total_out, "fee": fee,
                "coinbase": coinbase, "inputs_known": known,
                "quantum": tx["is_quantum_secured"], "witness": tx["witness_size_bytes"]}

    @staticmethod
    def _pub_party(p):
        d = {"coinbase": bool(p.get("coinbase")), "value": p.get("value")}
        if p.get("addr"):
            d["addr"] = encode_address(p["addr"])
        if "n" in p:
            d["n"] = p["n"]
            d["spent_by"] = p.get("spent_by")
        return d

    def _pub_tx(self, t, full=True):
        ins = [self._pub_party(i) for i in t["inputs"]]
        outs = [self._pub_party(o) for o in t["outputs"]]
        return {"txid": t["txid"], "height": t["height"], "timestamp": t["timestamp"],
                "confirmations": t["confirmations"], "fee": t["fee"], "coinbase": t["coinbase"],
                "total_out": t["total_out"], "inputs_known": t["inputs_known"],
                "quantum": t["quantum"], "witness": t["witness"],
                "in_count": len(ins), "out_count": len(outs),
                "inputs": ins[:MAX_LIST], "outputs": outs[:MAX_LIST]}

    def tx_view(self, txid):
        with self.lock:
            t = self._tx_info(txid)
            return self._pub_tx(t) if t else None

    def block_view(self, h):
        with self.lock:
            blk = self.blocks.get(h)
            if blk is None:
                return None
            miner, reward = self._miner(blk)
            txs = []
            for tx in blk["transactions"]:
                t = self._tx_info(tx["txid"])
                if t:
                    txs.append(self._pub_tx(t))
            return {"height": h, "timestamp": blk["timestamp"], "nonce": blk["nonce"],
                    "tx_count": blk["tx_count"], "previous_hash": blk["previous_hash"],
                    "merkle_root": blk["merkle_root"], "target": blk["target"],
                    "miner": miner, "reward": reward, "tip": self.tip,
                    "total_fees": sum(x["fee"] or 0 for x in txs), "txs": txs}

    def _addr_row(self, txid, me):
        t = self._tx_info(txid)
        recv = sum(o["value"] for o in t["outputs"] if o["addr"] == me)
        sent = sum(i["value"] for i in t["inputs"] if i["addr"] == me and i["value"])
        all_to_me = all(o["addr"] == me for o in t["outputs"])
        if sent and all_to_me:
            direction = "self"
        elif sent:
            direction = "out"
        else:
            direction = "in"
        pub = self._pub_tx(t)
        pub.update({"net": recv - sent, "recv": recv, "sent": sent, "direction": direction})
        return pub

    def address_page(self, me, offset=0, limit=PAGE_SIZE, with_summary=True):
        with self.lock:
            txids = list(self.addr_txs.get(me, ()))
            txids.sort(key=lambda x: (self.txs[x][0], x), reverse=True)
            rows = [self._addr_row(x, me) for x in txids[offset:offset + limit]]
            if not with_summary:
                return {"rows": rows, "total": len(txids)}

            received = sent = 0
            mined = 0
            first = last = None
            sent_to, recv_from = {}, {}
            history = []
            running = 0
            for txid in reversed(txids):  # oldest -> newest to build the balance chart
                t = self._tx_info(txid)
                r = sum(o["value"] for o in t["outputs"] if o["addr"] == me)
                s = sum(i["value"] for i in t["inputs"] if i["addr"] == me and i["value"])
                received += r
                sent += s
                running += r - s
                history.append([t["timestamp"], running])
                ts = t["timestamp"]
                first = ts if first is None else min(first, ts)
                last = ts if last is None else max(last, ts)
                if s:
                    for o in t["outputs"]:
                        if o["addr"] != me:
                            e = sent_to.setdefault(o["addr"], [0, 0])
                            e[0] += o["value"]
                            e[1] += 1
                elif r:
                    if t["coinbase"]:
                        mined += 1
                        e = recv_from.setdefault("coinbase", [0, 0])
                        e[0] += r
                        e[1] += 1
                    else:
                        senders = {}
                        for i in t["inputs"]:
                            if i["addr"] and i["value"]:
                                senders[i["addr"]] = senders.get(i["addr"], 0) + i["value"]
                        tot = sum(senders.values())
                        for a, v in senders.items():
                            e = recv_from.setdefault(a, [0, 0])
                            e[0] += int(r * v / tot) if tot else 0
                            e[1] += 1

            if len(history) > MAX_HISTORY:
                step = len(history) / MAX_HISTORY
                history = [history[int(i * step)] for i in range(MAX_HISTORY)] + [history[-1]]

            def top(d):
                items = sorted(d.items(), key=lambda kv: kv[1][0], reverse=True)[:30]
                return [{"addr": (None if a == "coinbase" else encode_address(a)),
                         "coinbase": a == "coinbase", "sats": v[0], "txs": v[1]}
                        for a, v in items]

            return {"rows": rows, "total": len(txids), "received": received, "sent": sent,
                    "mined": mined, "history": history,
                    "first_seen": first, "last_seen": last,
                    "sent_to": top(sent_to), "received_from": top(recv_from)}


# ----------------------------------------------------------------------------
# Web server
# ----------------------------------------------------------------------------
HEX64 = re.compile(r"^[0-9a-fA-F]{64}$")


def make_handler(index, rpc, price):
    page_bytes = PAGE.replace("__PRICE__", repr(float(price))).encode()

    class H(BaseHTTPRequestHandler):
        def log_message(self, *a):
            pass

        def _json(self, obj, code=200):
            body = json.dumps(obj).encode()
            self.send_response(code)
            self.send_header("Content-Type", "application/json; charset=utf-8")
            self.send_header("Content-Length", str(len(body)))
            self.send_header("Cache-Control", "no-store")
            self.end_headers()
            self.wfile.write(body)

        def do_GET(self):
            u = urlparse(self.path)
            q = parse_qs(u.query)
            try:
                if u.path == "/":
                    self.send_response(200)
                    self.send_header("Content-Type", "text/html; charset=utf-8")
                    self.send_header("Content-Length", str(len(page_bytes)))
                    self.end_headers()
                    self.wfile.write(page_bytes)
                elif u.path == "/api/status":
                    st = index.status()
                    try:
                        st["mempool"] = rpc.info().get("mempool_size")
                    except Exception:
                        st["mempool"] = None
                    self._json(st)
                elif u.path == "/api/latest":
                    tip = index.status()["tip"]
                    self._json(index.latest(tip, 15))
                elif u.path == "/api/addr_txs":
                    d = decode_address((q.get("a") or [""])[0])
                    if not d:
                        return self._json({"error": "bad address"}, 400)
                    off = max(0, int((q.get("offset") or ["0"])[0]))
                    self._json(index.address_page(d[1], off, PAGE_SIZE, with_summary=False))
                elif u.path == "/api/search":
                    self._json(self.search((q.get("q") or [""])[0].strip()))
                else:
                    self._json({"error": "not found"}, 404)
            except Exception as e:
                self._json({"error": str(e)}, 500)

        def _address_result(self, hash_hex):
            address = encode_address(hash_hex)
            bal = None
            try:
                bal = rpc.balance(address)
            except Exception:
                pass
            res = {"type": "address", "address": address, "hash": hash_hex, "balance": bal,
                   "page_size": PAGE_SIZE, "status": index.status()}
            res.update(index.address_page(hash_hex))
            return res

        def search(self, text):
            if not text:
                return {"type": "error", "message": "Type something to search"}
            if text.isdigit() and len(text) < 12:
                h = int(text)
                view = index.block_view(h)
                if view is None:
                    blk = None
                    try:
                        blk = rpc.block(h)
                    except Exception:
                        pass
                    if blk is None:
                        return {"type": "error", "message": f"No block at height {h}"}
                    return {"type": "error", "message": f"Block {h} is not indexed yet, please wait for indexing to finish."}
                return {"type": "block", "block": view}
            if HEX64.match(text):
                key = text.lower()
                view = index.tx_view(key)
                if view:
                    return {"type": "tx", "tx": view, "tip": index.status()["tip"]}
                with index.lock:
                    known_addr = key in index.addr_txs
                if known_addr:
                    return self._address_result(key)
                try:
                    status = rpc.tx_status(key).get("status")
                except Exception:
                    status = None
                if status == "PENDING":
                    return {"type": "pending", "txid": key}
                done = index.status()
                msg = "No transaction or address with this hash was found in the index."
                if done["indexed"] < done["total"]:
                    msg += f" (Indexing not finished: {done['indexed']}/{done['total']})"
                return {"type": "error", "message": msg}
            if text.startswith(HRP + "1"):
                dec = decode_address(text)
                if not dec:
                    return {"type": "error", "message": "Invalid address (Bech32m checksum failed)"}
                return self._address_result(dec[1])
            return {"type": "error",
                    "message": "Unsupported format: use a block height, a transaction hash (64 chars) or a qbtc1... address"}

    return H


PAGE = r"""<!doctype html>
<html lang="en" dir="ltr">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>QBTC Explorer</title>
<style>
:root{--bg:#fff;--page:#f7f7f8;--card:#fff;--row:#f8f8f9;--text:#1a1a1f;--muted:#7b7d85;--line:#ececef;--acc:#ec8b3a;--soft:#fdeee0;--soft2:#fbe3cf;--ok:#1fb27a;--okbg:#e3f6ee;--bad:#e0555c;--badbg:#fdeaeb;--inp:#fff;--btn:#111}
:root[data-theme=dark]{--bg:#0f1115;--page:#0b0d11;--card:#14171d;--row:#181c24;--text:#eceef2;--muted:#8d93a1;--line:#242934;--acc:#f19a4d;--soft:#2a2016;--soft2:#3a2a1b;--ok:#3ddc97;--okbg:#12281f;--bad:#f0777d;--badbg:#2e1719;--inp:#14171d;--btn:#f19a4d}
@media (prefers-color-scheme:dark){:root:not([data-theme=light]){--bg:#0f1115;--page:#0b0d11;--card:#14171d;--row:#181c24;--text:#eceef2;--muted:#8d93a1;--line:#242934;--acc:#f19a4d;--soft:#2a2016;--soft2:#3a2a1b;--ok:#3ddc97;--okbg:#12281f;--bad:#f0777d;--badbg:#2e1719;--inp:#14171d;--btn:#f19a4d}}
*{box-sizing:border-box}
body{margin:0;background:var(--page);color:var(--text);font:14px/1.6 system-ui,-apple-system,"Segoe UI",Roboto,sans-serif}
.nav{background:var(--bg);border-bottom:1px solid var(--line);position:sticky;top:0;z-index:5}
.nav .in{max-width:1100px;margin:0 auto;padding:12px 16px;display:flex;gap:12px;align-items:center}
.logo{width:40px;height:40px;border-radius:10px;background:var(--text);color:var(--bg);display:flex;align-items:center;justify-content:center;font-weight:800;font-size:20px;cursor:pointer;flex:none}
.search{flex:1;display:flex;align-items:center;gap:8px;border:1px solid var(--line);background:var(--inp);border-radius:10px;padding:5px 6px 5px 12px;min-width:0}
.search input{flex:1;min-width:0;border:0;outline:0;background:transparent;color:var(--text);font-size:14px;padding:6px 4px}
.search button{width:34px;height:34px;border:0;border-radius:8px;background:var(--btn);color:var(--bg);font-size:16px;cursor:pointer;flex:none}
.icon-btn{width:36px;height:36px;border-radius:50%;border:0;background:var(--line);color:var(--text);cursor:pointer;flex:none}
.wrap{max-width:1100px;margin:0 auto;padding:0 16px 40px}
.mono{font-family:ui-monospace,Menlo,Consolas,monospace;word-break:break-all}
a.l{color:var(--acc);cursor:pointer;text-decoration:none}
a.l:hover{text-decoration:underline}
.stats{display:flex;gap:18px;flex-wrap:wrap;color:var(--muted);font-size:12px;padding:12px 2px}
.stats b{color:var(--text)}
.warn{background:var(--soft);color:var(--acc);border-radius:10px;padding:10px 14px;margin:12px 0;font-size:13px}
.profile{display:flex;gap:18px;align-items:flex-start;padding:22px 4px 8px}
.avatar{width:72px;height:72px;border-radius:50%;display:flex;align-items:center;justify-content:center;font-size:28px;font-weight:800;color:#1a1a1f;flex:none}
.pname{font-size:22px;font-weight:700;margin:2px 0 8px}
.badges{display:flex;gap:8px;flex-wrap:wrap}
.badge{display:inline-flex;align-items:center;gap:5px;background:var(--soft);color:var(--acc);border-radius:20px;padding:3px 12px;font-size:13px}
.badge.ok{background:var(--okbg);color:var(--ok)}
.badge.bad{background:var(--badbg);color:var(--bad)}
.badge.gray{background:var(--line);color:var(--muted)}
.addrbox{display:flex;gap:10px;align-items:center;margin:14px 4px 0}
.addrico{width:36px;height:36px;border-radius:8px;background:var(--acc);color:#fff;display:flex;align-items:center;justify-content:center;font-size:16px;flex:none}
.addrbox .lbl{font-size:11px;color:var(--muted)}
.addrbox .val{font-size:13px}
.copy{border:0;background:transparent;color:var(--muted);cursor:pointer;font-size:13px;padding:0 4px}
.desc{margin:12px 4px 0;font-size:13px;color:var(--text)}
.banner{background:var(--soft);border-radius:18px;padding:18px 22px;margin:18px 0}
.banner .k{font-size:12px;color:var(--muted)}
.banner .v{font-size:26px;font-weight:600}
.banner .v small{font-size:14px;color:var(--muted);font-weight:400}
.banner .usd{font-size:13px;color:var(--muted);margin-top:2px}
.price{background:var(--soft);color:var(--text);border-radius:12px;padding:10px 14px;margin:12px 0 0;font-size:13px}
.price b{color:var(--acc)}
.tabs{display:flex;justify-content:center;gap:6px;border-bottom:1px solid var(--line);margin:10px 0 0}
.tab{padding:12px 22px;cursor:pointer;color:var(--muted);border-bottom:2px solid transparent;font-weight:500}
.tab.on{color:var(--text);border-color:var(--text);font-weight:700}
.sec{padding:20px 4px}
.sec h3{margin:0 0 14px;font-size:14px;color:var(--muted);font-weight:500}
.sum{display:grid;grid-template-columns:1.3fr 1fr 1fr;gap:18px 26px}
.sum .txt{color:var(--muted);font-size:12px;line-height:1.9}
.sum .item{margin-bottom:18px}
.sum .item .k{color:var(--muted);font-size:12px}
.sum .item .v{font-weight:700;font-size:13px}
.sum .item .u{color:var(--muted);font-size:12px}
.hr{border:0;border-top:1px solid var(--line);margin:6px 0}
.tx{border-bottom:1px solid var(--line);background:var(--row)}
.tx .row{display:grid;grid-template-columns:48px 1.2fr 1.2fr 1.2fr 28px;gap:12px;align-items:center;padding:18px 14px}
.ico{width:48px;height:48px;border-radius:50%;display:flex;align-items:center;justify-content:center;font-size:20px;background:var(--okbg);color:var(--ok)}
.ico.out{background:var(--badbg);color:var(--bad)}
.ico.self{background:var(--line);color:var(--muted)}
.ico.cb{background:var(--soft);color:var(--acc)}
.chev{cursor:pointer;color:var(--text);font-size:18px;text-align:center;transition:.15s;user-select:none}
.chev.on{transform:rotate(180deg)}
.amt{text-align:right;font-size:13px}
.amt .a{font-weight:700;font-size:14px}
.amt .a.pos{color:var(--ok)}.amt .a.neg{color:var(--bad)}
.amt .a small{color:var(--muted);font-weight:400;font-size:12px}
.amt .f{color:var(--muted);font-size:12px}
.amt .f i{font-style:normal;color:var(--bad)}
.ft{font-size:13px}
.ft div{display:flex;gap:8px;align-items:baseline}
.ft .k{color:var(--text);font-weight:600;min-width:34px}
.idc .id{color:var(--acc);font-size:13px;display:flex;gap:4px;align-items:center}
.idc .id .lb{color:var(--muted)}
.idc .dt{color:var(--muted);font-size:12px;margin-top:4px}
.detail{display:none;padding:0 14px 16px}
.detail.on{display:block}
.detail h4{margin:12px 0 6px;font-size:13px;color:var(--muted);font-weight:500}
table{width:100%;border-collapse:collapse}
th,td{padding:8px 6px;border-bottom:1px solid var(--line);text-align:start;vertical-align:top;font-size:13px}
th{color:var(--muted);font-weight:500}
.ts{overflow-x:auto}
.card{background:var(--card);border:1px solid var(--line);border-radius:14px;padding:16px;margin:14px 0}
.kv{display:grid;grid-template-columns:170px 1fr;gap:8px 14px}
.kv div:nth-child(odd){color:var(--muted)}
.btn{display:block;width:100%;padding:12px;margin:16px 0 0;border:1px solid var(--line);background:var(--card);color:var(--acc);border-radius:12px;cursor:pointer;font-size:14px}
.msg{color:var(--bad)}
h1{font-size:20px;margin:0}
h2{font-size:15px;margin:0 0 10px}
.note{color:var(--muted);font-size:12px;margin:6px 0}
.title{display:flex;align-items:center;gap:10px;flex-wrap:wrap}
.cpgrid{display:grid;grid-template-columns:1fr 1fr;gap:14px}
.chart svg{width:100%;height:auto}
@media (max-width:700px){
 .sum{grid-template-columns:1fr 1fr}.sum .txt{grid-column:1/-1}
 .tx .row{grid-template-columns:1fr 1fr 28px;grid-template-areas:"i i c" "a a a" "f f f"}
 .tx .row .chev{grid-area:c}.tx .row .amt{grid-area:a;text-align:left}.tx .row .ft{grid-area:f}.tx .row .idc{grid-area:i}
 .ico{display:none}.kv{grid-template-columns:1fr}.cpgrid{grid-template-columns:1fr}
}
</style>
</head>
<body>
<div class="nav"><div class="in">
 <div class="logo" id="home">Q</div>
 <form class="search" id="f"><input id="q" placeholder="Enter an address, block, or transaction..." autocomplete="off"><button title="Search">&#8981;</button></form>
 <button class="icon-btn" id="theme" title="Light / dark mode">&#9680;</button>
</div></div>
<div class="wrap">
 <div class="stats" id="stats">Loading...</div>
 <div id="result"></div>
 <div class="card" id="latestcard"><h2>Latest blocks</h2><div class="ts" id="latest"></div></div>
</div>
<script>
const $=s=>document.querySelector(s);
const SATS=1e8;
const PRICE=__PRICE__; // USD per 1 QBTC (approx.)
const fmt=s=>s==null?'—':(s/SATS).toLocaleString('en',{minimumFractionDigits:8,maximumFractionDigits:8});
const fmtShort=s=>s==null?'—':(s/SATS).toLocaleString('en',{minimumFractionDigits:2,maximumFractionDigits:8});
const fmtSats=s=>s==null?'—':Number(s).toLocaleString('en')+' sats';
const usd=s=>{if(s==null)return '—';const v=Math.abs(s/SATS*PRICE);
  const d=v>=0.01||v===0?2:(v>=0.0001?4:6);
  return '$'+v.toLocaleString('en',{minimumFractionDigits:d,maximumFractionDigits:d})};
const PRICE_TXT=PRICE.toLocaleString('en',{minimumFractionDigits:6,maximumFractionDigits:6});
const pad=n=>String(n).padStart(2,'0');
const when=t=>{if(!t)return '—';const d=new Date(t*1000);return pad(d.getMonth()+1)+'/'+pad(d.getDate())+'/'+d.getFullYear()+', '+pad(d.getHours())+':'+pad(d.getMinutes())+':'+pad(d.getSeconds())};
const sAddr=a=>a?a.slice(0,5)+'-'+a.slice(-4):'';
const sTx=t=>t.slice(0,4)+'-'+t.slice(-4);
function el(tag,attrs,...kids){
  const e=document.createElement(tag);
  for(const[k,v]of Object.entries(attrs||{})){
    if(k==='class')e.className=v;else if(k==='click')e.onclick=v;else e.setAttribute(k,v);
  }
  for(const k of kids.flat()){if(k==null||k===false)continue;e.append(k.nodeType?k:document.createTextNode(String(k)));}
  return e;
}
const link=(text,q,cls)=>el('a',{class:'l '+(cls===undefined?'mono':cls),click:()=>go(q),title:q},text);
async function api(p){const r=await fetch(p);return r.json()}
function kv(rows){const d=el('div',{class:'kv'});for(const[k,v]of rows){d.append(el('div',{},k),el('div',{},v))}return d}
function copyBtn(text){const b=el('button',{class:'copy',title:'Copy'},'⧉');b.onclick=async()=>{try{await navigator.clipboard.writeText(text);b.textContent='✓'}catch(e){b.textContent='×'}setTimeout(()=>b.textContent='⧉',1500)};return b}
const PALETTE=['#f6b26b','#8fd3b6','#9ec5fe','#f4a6c0','#c3b1e1','#f7d774','#a8e0e8','#f0a58f'];
const colorOf=s=>PALETTE[(parseInt(s.slice(-2),36)||0)%PALETTE.length];
const priceNote=()=>el('div',{class:'price'},'Price per 1 QBTC: ',el('b',{},'$'+PRICE_TXT),' (approx. $'+PRICE_TXT+').');

/* ---------- General status ---------- */
async function stats(){
  const s=await api('/api/status');
  const box=$('#stats');box.replaceChildren();
  if(!s.node_ok){box.append(el('span',{class:'msg'},'⚠️ Cannot reach the data source: '+s.error));return}
  box.append(el('span',{},'Height: ',el('b',{},s.tip)),
    el('span',{},'Mempool: ',el('b',{},s.mempool??'?')),
    el('span',{},'Indexed: ',el('b',{},s.indexed+'/'+s.total)),
    el('span',{},'1 QBTC ≈ ',el('b',{},'$'+PRICE_TXT)));
}
async function latest(){
  const rows=await api('/api/latest');
  const t=el('table',{},el('thead',{},el('tr',{},el('th',{},'Block'),el('th',{},'Time'),el('th',{},'Transactions'),el('th',{},'Miner'),el('th',{},'Reward'))));
  const b=el('tbody');
  for(const r of rows)b.append(el('tr',{},el('td',{},link(r.height,String(r.height),'')),el('td',{},when(r.timestamp)),el('td',{},r.tx_count),
    el('td',{},r.miner?link(sAddr(r.miner),r.miner):'—'),el('td',{class:'mono'},fmtShort(r.reward)+' QBTC ('+usd(r.reward)+')')));
  t.append(b);$('#latest').replaceChildren(t);
}

/* ---------- Inputs / outputs tables ---------- */
function partyTable(items,me,kind){
  const t=el('table',{},el('thead',{},el('tr',{},el('th',{},'#'),el('th',{},'Address'),el('th',{},'Value'),kind==='out'?el('th',{},'Status'):null)));
  const b=el('tbody');
  items.forEach((p,i)=>{
    const who=p.coinbase?el('span',{class:'badge gray'},'Coinbase'):(p.addr?el('span',{},link(p.addr,p.addr),p.addr===me?el('span',{class:'badge'},'This address'):null):'Unknown (incomplete index)');
    let st=null;
    if(kind==='out')st=el('td',{},p.spent_by?el('span',{},'Spent in ',link(sTx(p.spent_by),p.spent_by)):el('span',{class:'badge ok'},'Unspent'));
    b.append(el('tr',{},el('td',{},p.n!=null?p.n:i),el('td',{},who),el('td',{class:'mono'},fmt(p.value)+' QBTC ('+usd(p.value)+')'),st));
  });
  t.append(b);return el('div',{class:'ts'},t);
}

/* ---------- Transaction row (blockchain.com style) ---------- */
function txCard(x,me){
  const dir=me!=null?x.direction:'in';
  const icoCls=x.coinbase?'cb':(dir==='out'?'out':(dir==='self'?'self':''));
  const icoTxt=x.coinbase?'⛏':(dir==='out'?'↗':(dir==='self'?'⇄':'↘'));
  const detail=el('div',{class:'detail'},
    el('h4',{},'Inputs ('+x.in_count+')'),partyTable(x.inputs,me,'in'),
    el('h4',{},'Outputs ('+x.out_count+')'),partyTable(x.outputs,me,'out'),
    el('div',{class:'note'},'Quantum signature: '+(x.quantum?'yes':'no (coinbase)')+' — witness size: '+x.witness+' bytes — '+(x.confirmations>0?x.confirmations+' confirmations':'unconfirmed')));
  const chev=el('div',{class:'chev',click:()=>{detail.classList.toggle('on');chev.classList.toggle('on')}},'⌄');

  // From
  let from;
  if(x.coinbase)from=el('span',{class:'badge gray'},'Coinbase');
  else{
    const seen=[];for(const p of x.inputs){if(p.addr&&!seen.includes(p.addr))seen.push(p.addr)}
    from=seen.length?el('span',{},link(sAddr(seen[0]),seen[0]),seen.length>1||x.in_count>x.inputs.length?el('span',{class:'note'},' +'+(Math.max(seen.length,x.in_count)-1)):null):el('span',{class:'note'},'Unknown');
  }
  // To
  let to;
  if(x.out_count===1&&x.outputs[0].addr)to=link(sAddr(x.outputs[0].addr),x.outputs[0].addr);
  else to=el('span',{class:'note'},x.out_count+' outputs');
  const ft=el('div',{class:'ft'},el('div',{},el('span',{class:'k'},'From'),from),el('div',{style:'margin-top:6px'},el('span',{class:'k'},'To'),to));

  // Amount
  let a;
  if(me!=null){
    const cls=x.net>0?'pos':(x.net<0?'neg':'');
    const sign=x.net>0?'+':(x.net<0?'−':'');
    a=el('div',{class:'a '+cls},sign+fmt(Math.abs(x.net))+' QBTC ',el('small',{},'· '+usd(x.net)));
  }else a=el('div',{class:'a'},fmt(x.total_out)+' QBTC ',el('small',{},'· '+usd(x.total_out)));
  const amt=el('div',{class:'amt'},a,el('div',{class:'f'},x.coinbase?'Mining reward':el('span',{},el('i',{},'Fee'),' '+(x.fee==null?'unknown':fmtSats(x.fee)+' · '+usd(x.fee)))));

  const idc=el('div',{class:'idc'},
    el('div',{class:'id'},el('span',{class:'lb'},'Txn ID:'),el('a',{class:'l mono',click:()=>go(x.txid),title:x.txid},sTx(x.txid)),copyBtn(x.txid)),
    el('div',{class:'dt'},when(x.timestamp)));

  return el('div',{class:'tx'},
    el('div',{class:'row'},el('div',{class:'ico '+icoCls},icoTxt),idc,ft,amt,chev),
    detail);
}

/* ---------- Balance chart ---------- */
function chartBox(h){
  const box=el('div',{class:'sec chart'},el('h3',{},'Balance history (QBTC)'));
  if(!h||h.length<2){box.append(el('div',{class:'note'},'Not enough data to draw the chart.'));return box}
  const W=700,H=280,P=56;
  const xs=h.map(p=>p[0]),ys=h.map(p=>p[1]/SATS);
  const x0=Math.min(...xs),x1=Math.max(...xs),y0=Math.min(0,...ys),y1=Math.max(...ys,y0+1e-8);
  const X=t=>P+(x1===x0?0:(t-x0)/(x1-x0))*(W-P-12);
  const Y=v=>H-26-((v-y0)/(y1-y0))*(H-26-14);
  let pts='';let prev=null;
  h.forEach(p=>{const x=X(p[0]).toFixed(1),y=Y(p[1]/SATS).toFixed(1);if(prev!==null)pts+=x+','+prev+' ';pts+=x+','+y+' ';prev=y});
  const area='M'+X(x0).toFixed(1)+','+Y(y0).toFixed(1)+' L'+pts.trim().split(' ').join(' L')+' L'+X(x1).toFixed(1)+','+Y(y0).toFixed(1)+' Z';
  const nf=v=>v.toLocaleString('en',{maximumFractionDigits:4});
  const d1=new Date(x0*1000).toLocaleDateString('en-GB'),d2=new Date(x1*1000).toLocaleDateString('en-GB');
  box.insertAdjacentHTML('beforeend',
   '<svg viewBox="0 0 '+W+' '+H+'" xmlns="http://www.w3.org/2000/svg">'+
   '<path d="'+area+'" fill="var(--acc)" opacity="0.15"/>'+
   '<polyline points="'+pts+'" fill="none" stroke="var(--acc)" stroke-width="2"/>'+
   '<line x1="'+P+'" y1="'+Y(y0)+'" x2="'+(W-12)+'" y2="'+Y(y0)+'" stroke="var(--line)"/>'+
   '<text x="4" y="'+(Y(y1)+4)+'" font-size="11" fill="var(--muted)">'+nf(y1)+'</text>'+
   '<text x="4" y="'+(Y(y0)+4)+'" font-size="11" fill="var(--muted)">'+nf(y0)+'</text>'+
   '<text x="'+P+'" y="'+(H-6)+'" font-size="11" fill="var(--muted)">'+d1+'</text>'+
   '<text x="'+(W-12)+'" y="'+(H-6)+'" font-size="11" text-anchor="end" fill="var(--muted)">'+d2+'</text></svg>');
  return box;
}

/* ---------- Address page ---------- */
function showAddr(r){
  const bal=r.balance;
  const box=el('div',{});
  const st=r.status;
  if(st&&st.indexed<st.total)box.append(el('div',{class:'warn'},'⏳ Indexing is not finished ('+st.indexed+'/'+st.total+'): received/sent totals and the transaction history may be incomplete until it completes.'));

  const idxBal=(r.received||0)-(r.sent||0);
  const total=bal?(bal.confirmed_sats+(bal.locked_sats||0)):idxBal;
  const initials=r.address.slice(5,7).toUpperCase();

  const badges=el('div',{class:'badges'});
  if(r.mined>0)badges.append(el('span',{class:'badge'},'⛏ Miner'));
  badges.append(el('span',{class:'badge'},'Bech32m'),el('span',{class:'badge'},'ML-DSA-65 (quantum)'));

  box.append(
    el('div',{class:'profile'},
      el('div',{class:'avatar',style:'background:'+colorOf(r.address)},initials),
      el('div',{},el('div',{class:'pname'},r.mined>0?'Miner address':'QBTC address'),badges)),
    el('div',{class:'addrbox'},el('div',{class:'addrico'},'▣'),
      el('div',{},el('div',{class:'lbl'},'QBTC address'),el('div',{class:'val mono'},r.address,copyBtn(r.address)))),
    el('div',{class:'desc'},
      r.mined>0?'This address received mining rewards from '+r.mined+' blocks on the QBTC chain.':'Key hash: ',
      r.mined>0?null:el('span',{class:'mono',style:'font-size:12px'},r.hash)),
    el('div',{class:'banner'},el('div',{class:'k'},'QBTC balance'),
      el('div',{class:'v'},fmt(total)+' ',el('small',{},'QBTC · '+usd(total)))),
    priceNote());

  const tabs=el('div',{class:'tabs'});
  const body=el('div',{});

  // --- Wallet tab ---
  const sumLines=[
    'This address has made '+r.total.toLocaleString('en')+' transactions on the QBTC blockchain.',
    'It has received a total of '+fmt(r.received)+' QBTC ('+usd(r.received)+').',
    'It has sent a total of '+fmt(r.sent)+' QBTC ('+usd(r.sent)+').',
    'The current value of this address is '+fmt(total)+' QBTC ('+usd(total)+').'];
  const it=(k,v,u)=>el('div',{class:'item'},el('div',{class:'k'},k),el('div',{class:'v'},v),u?el('div',{class:'u'},u):null);
  const vol=(r.received||0)+(r.sent||0);
  const summary=el('div',{class:'sec'},el('h3',{},'Summary'),
    el('div',{class:'sum'},
      el('div',{class:'txt'},sumLines.map(s=>el('div',{},s))),
      el('div',{},it('Total received',fmt(r.received)+' QBTC',usd(r.received)),it('Total volume',fmt(vol)+' QBTC',usd(vol)),it('First activity',when(r.first_seen))),
      el('div',{},it('Total sent',fmt(r.sent)+' QBTC',usd(r.sent)),it('Transactions',r.total.toLocaleString('en')),it('Last activity',when(r.last_seen)))));
  if(bal)summary.append(el('div',{class:'sum',style:'margin-top:4px'},
      el('div',{}),
      el('div',{},it('Pending (mempool)',fmt(bal.pending_sats)+' QBTC',usd(bal.pending_sats)),it('Locked (coinbase)',fmt(bal.locked_sats)+' QBTC',usd(bal.locked_sats))),
      el('div',{},it('Available (confirmed)',fmt(bal.confirmed_sats)+' QBTC',usd(bal.confirmed_sats)),it('UTXO count',bal.spendable_utxos))));

  let offset=r.rows.length;
  const txs=el('div',{});
  r.rows.forEach(x=>txs.append(txCard(x,r.address)));
  const loadMore=el('button',{class:'btn'},'Load more');
  loadMore.onclick=async()=>{
    loadMore.textContent='Loading...';
    const d=await api('/api/addr_txs?a='+encodeURIComponent(r.address)+'&offset='+offset);
    d.rows.forEach(x=>txs.append(txCard(x,r.address)));
    offset+=d.rows.length;
    if(offset>=r.total)loadMore.remove();else loadMore.textContent='Load more ('+(r.total-offset)+' remaining)';
  };
  const txSec=el('div',{class:'sec'},el('h3',{},'Transactions'),txs,r.total>offset?loadMore:null);
  if(!r.total)txSec.append(el('div',{class:'note'},'No transactions found for this address in the index.'));
  const walletPane=el('div',{},summary,el('hr',{class:'hr'}),txSec);

  // --- Chart tab ---
  const chartPane=chartBox(r.history);

  // --- Counterparties tab ---
  function cp(list,title,note){
    const t=el('table',{},el('thead',{},el('tr',{},el('th',{},'Address'),el('th',{},'Transactions'),el('th',{},'Value'))));
    const b=el('tbody');
    for(const c of list)b.append(el('tr',{},el('td',{},c.coinbase?el('span',{class:'badge gray'},'Coinbase (mining)'):link(c.addr,c.addr)),el('td',{},c.txs),el('td',{class:'mono'},fmt(c.sats)+' QBTC ('+usd(c.sats)+')')));
    t.append(b);
    return el('div',{},el('h2',{},title),el('div',{class:'note'},note),list.length?el('div',{class:'ts'},t):el('div',{class:'note'},'None.'));
  }
  const cpPane=el('div',{class:'sec'},el('div',{class:'cpgrid'},
    cp(r.received_from,'Who sent to this address','Estimate: when a transaction has several senders, the amount is split in proportion to their inputs. Top 30.'),
    cp(r.sent_to,'Who this address sent to','Excludes change returned to the same address. Top 30.')));

  const panes={'Wallet':walletPane,'Chart':chartPane,'Counterparties':cpPane};
  let first=true;
  for(const name of Object.keys(panes)){
    const tab=el('div',{class:'tab'+(first?' on':'')},name);
    panes[name].style.display=first?'':'none';
    tab.onclick=()=>{for(const[n,p]of Object.entries(panes))p.style.display=n===name?'':'none';[...tabs.children].forEach(c=>c.classList.toggle('on',c===tab))};
    tabs.append(tab);body.append(panes[name]);first=false;
  }
  box.append(tabs,body);
  return box;
}

/* ---------- Transaction page ---------- */
function showTx(r){
  const x=r.tx;
  const c=el('div',{class:'card'},
    el('div',{class:'title'},el('h1',{},'Transaction'),el('span',{class:'badge '+(x.confirmations>0?'ok':'bad')},x.confirmations>0?'Confirmed':'Unconfirmed'),x.coinbase?el('span',{class:'badge gray'},'Coinbase'):null),
    el('div',{class:'mono',style:'margin-top:8px;font-size:13px'},x.txid,copyBtn(x.txid)),
    el('div',{style:'margin-top:14px'},kv([
      ['Block',link('#'+x.height,String(x.height),'')],
      ['Confirmations',x.confirmations],
      ['Time',when(x.timestamp)],
      ['Total output',fmt(x.total_out)+' QBTC ('+usd(x.total_out)+')'],
      ['Fee',x.coinbase?'—':(x.fee==null?'Unknown (incomplete index)':fmtSats(x.fee)+' ('+usd(x.fee)+')')],
      ['Quantum signature',x.quantum?'Yes (ML-DSA)':'No (coinbase)'],
      ['Witness size',x.witness+' bytes']])),
    priceNote());
  const wrap=el('div',{},c);
  wrap.append(el('div',{class:'card'},
    el('h2',{},'Inputs ('+x.in_count+')'),
    x.coinbase?el('span',{class:'badge gray'},'Coinbase (mining reward — no previous inputs)'):partyTable(x.inputs,null,'in'),
    el('h2',{style:'margin-top:16px'},'Outputs ('+x.out_count+')'),partyTable(x.outputs,null,'out')));
  return wrap;
}

/* ---------- Block page ---------- */
function showBlock(r){
  const b=r.block;
  const c=el('div',{class:'card'},
    el('div',{class:'title'},el('h1',{},'Block #'+b.height),el('span',{class:'badge ok'},(b.tip-b.height+1)+' confirmations')),
    el('div',{style:'margin-top:14px'},kv([
      ['Time',when(b.timestamp)],
      ['Transactions',b.tx_count],
      ['Miner',b.miner?link(b.miner,b.miner):'—'],
      ['Block reward',fmt(b.reward)+' QBTC ('+usd(b.reward)+')'],
      ['Total fees',fmtSats(b.total_fees)+' ('+usd(b.total_fees)+')'],
      ['Nonce',b.nonce],
      ['Previous block',el('span',{class:'mono'},b.previous_hash)],
      ['Merkle root',el('span',{class:'mono'},b.merkle_root)]])),
    el('div',{style:'margin-top:12px;display:flex;gap:16px'},
      b.height>0?el('a',{class:'l',click:()=>go(String(b.height-1))},'← Previous block'):null,
      b.height<b.tip?el('a',{class:'l',click:()=>go(String(b.height+1))},'Next block →'):null),
    el('div',{class:'note'},'The block ID here is its height; the RPC interface does not return the block hash itself.'));
  const wrap=el('div',{},c,el('h2',{style:'margin:18px 4px 0'},'Transactions'));
  b.txs.forEach(x=>wrap.append(txCard(x,null)));
  return wrap;
}

async function go(q){
  $('#q').value=q;
  const res=$('#result');res.replaceChildren(el('div',{class:'card'},'Searching...'));
  let r;
  try{r=await api('/api/search?q='+encodeURIComponent(q))}catch(e){r={type:'error',message:String(e)}}
  let node;
  if(r.type==='block')node=showBlock(r);
  else if(r.type==='tx')node=showTx(r);
  else if(r.type==='address')node=showAddr(r);
  else if(r.type==='pending')node=el('div',{class:'card'},'⏳ This transaction is in the mempool and has not been included in a block yet.',el('div',{class:'mono'},r.txid));
  else node=el('div',{class:'card msg'},r.message||r.error||'Error');
  res.replaceChildren(node);
  $('#latestcard').style.display='none';
  location.hash=encodeURIComponent(q);
  window.scrollTo({top:0});
}
$('#f').onsubmit=e=>{e.preventDefault();const q=$('#q').value.trim();if(q)go(q)};
$('#home').onclick=()=>{$('#result').replaceChildren();$('#q').value='';$('#latestcard').style.display='';history.replaceState(null,'',location.pathname)};
$('#theme').onclick=()=>{
  const cur=document.documentElement.getAttribute('data-theme')||(matchMedia('(prefers-color-scheme:dark)').matches?'dark':'light');
  const next=cur==='dark'?'light':'dark';
  document.documentElement.setAttribute('data-theme',next);
  try{localStorage.setItem('qbtc-theme',next)}catch(e){}
};
try{const t=localStorage.getItem('qbtc-theme');if(t)document.documentElement.setAttribute('data-theme',t)}catch(e){}
stats();latest();
setInterval(()=>{stats();if($('#latestcard').style.display!=='none')latest()},15000);
if(location.hash.length>1)go(decodeURIComponent(location.hash.slice(1)));
</script>
</body>
</html>
"""


def main():
    ap = argparse.ArgumentParser(description="QBTC blockchain explorer")
    ap.add_argument("--rpc", default=os.environ.get("QBTC_RPC", "https://explorer.qbtc-core.org"))
    ap.add_argument("--host", default="0.0.0.0")
    ap.add_argument("--port", type=int, default=int(os.environ.get("PORT", "8080")))
    ap.add_argument("--delay", type=float, default=0.02)
    ap.add_argument("--cache", default="explorer_cache.json")
    ap.add_argument("--price", type=float, default=PRICE_USD,
                    help="price of one QBTC in USD (default 0.001126)")
    args = ap.parse_args()

    rpc = Rpc(args.rpc)
    rpc.delay = max(0.0, args.delay)
    index = Index(rpc, args.cache)
    threading.Thread(target=index.run, daemon=True).start()

    srv = ThreadingHTTPServer((args.host, args.port), make_handler(index, rpc, args.price))
    print(f"QBTC Explorer: http://{args.host}:{args.port}  (RPC: {args.rpc}, price: ${args.price})")
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        print("\nSaving index...")
        index.save_cache()


if __name__ == "__main__":
    main()
