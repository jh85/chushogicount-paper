#!/usr/bin/env python3
"""Test 3 + lishogi check: replay saved certificates in the native engine under `rules jcsa`
and `rules lishogi`: every move must be legal at its ply and the final board must equal
the target.  Certificates are streamed in batches of --batch (M-F's 503 180 do not fit in
memory); --resume keeps the records already written and skips their (stratum, seed).
Usage: replay_native.py out/runs/X_certs.jsonl.gz --procs 14 [--batch 2000] [--resume]"""
import argparse, gzip, json, sys, time
from collections import Counter
from multiprocessing import Pool
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
_c = {}


def _init():
    from jcsa.native import NativeEngine
    _c["nj"] = NativeEngine("jcsa")
    _c["nl"] = NativeEngine("lishogi")


def replay(eng, moves, target_sfen):
    from count.sfen import INITIAL, parse
    eng.position(INITIAL)
    for i, mv in enumerate(moves):
        if mv not in eng.legal():
            return False, i, mv
        eng.move(mv)
    final = parse(eng.sfen())[0]
    if final != parse(target_sfen)[0]:
        return False, len(moves), "final board differs"
    return True, None, None


def _work(rec):
    out = {"stratum": rec["stratum"], "seed": rec["seed"], "sfen": rec["sfen"]}
    if not rec.get("moves"):
        out["skipped"] = True
        return out
    for mode in ("lishogi", "jcsa"):
        ok, ply, info = replay(_c["nl" if mode == "lishogi" else "nj"], rec["moves"], rec["sfen"])
        out[mode] = ok
        if not ok:
            out[mode + "_fail"] = {"ply": ply, "info": info}
    return out


def _batches(path, n, skip):
    batch = []
    for line in gzip.open(path, "rt"):
        rec = json.loads(line)
        if (rec["stratum"], rec["seed"]) in skip:
            continue
        batch.append(rec)
        if len(batch) == n:
            yield batch
            batch = []
    if batch:
        yield batch


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("certs")
    ap.add_argument("--procs", type=int, default=14)
    ap.add_argument("--batch", type=int, default=2000)
    ap.add_argument("--resume", action="store_true")
    a = ap.parse_args()
    out = a.certs.replace("_certs.jsonl.gz", "_native_replay.jsonl")
    c = Counter()
    fails = []
    done = []
    if a.resume and Path(out).exists():
        for line in open(out):
            try:
                done.append(json.loads(line))
            except json.JSONDecodeError:             # a line cut off by a stop: dropped
                break
        Path(out).write_text("".join(json.dumps(r) + "\n" for r in done))
    skip = {(r["stratum"], r["seed"]) for r in done}

    def tally(r):
        if r.get("skipped"):
            c["skipped (no moves)"] += 1
            return
        c["replayed"] += 1
        for mode in ("lishogi", "jcsa"):
            c[f"{mode} ok"] += r[mode]
            if not r[mode]:
                fails.append((mode, r["sfen"], r[mode + "_fail"]))

    for r in done:
        tally(r)
    print(f"{len(done)} already replayed", flush=True)
    t0 = time.time()
    i = len(done)
    with Pool(a.procs, initializer=_init) as pool, open(out, "a") as fh:
        for batch in _batches(a.certs, a.batch, skip):
            for r in pool.imap_unordered(_work, batch, chunksize=8):
                fh.write(json.dumps(r) + "\n")
                tally(r)
                i += 1
                if i % 2000 == 0:
                    print(f"  ... {i} {dict(c)} {time.time() - t0:.0f}s", flush=True)
            fh.flush()
    print(f"done: {dict(c)}; failures {len(fails)}; {time.time() - t0:.0f}s")
    for f in fails[:40]:
        print("  FAIL", f)


if __name__ == "__main__":
    main()
