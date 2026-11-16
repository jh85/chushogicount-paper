#!/usr/bin/env python3
"""Supplementary lower end L' (exploratory; runs.md, "M-E follow-up"): the registered bracket
of a main run with the follow-up's certificates counted as certified.

The formula is the registered one: estimate.registered_brackets is called unchanged on the
main run's records, in which each non-terminal sample certified by followup.py is marked
ok (and jcsa_ok if its certificate also replays under JCSA).  Nothing else changes: I10
samples stay excluded, the remaining unresolved samples count as unreachable, the cap is
the registered cap.  Without --followup the script reproduces the registered line.

Usage: python3 src/plan/followup_bracket.py --records out/runs/<main>.jsonl [--followup out/runs/<main>_followup.jsonl ...] (repeatable)
"""
import argparse
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from count.candidates import chu_setup, count      # noqa: E402
from plan.estimate import registered_brackets      # noqa: E402


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--records", required=True)
    ap.add_argument("--followup", action="append", default=[], help="repeatable")
    a = ap.parse_args()
    recs = [json.loads(l) for l in open(a.records)]
    rescued = {}
    for path in a.followup:
        for r in map(json.loads, open(path)):
            if r["certified"]:
                rescued[r["seed"]] = bool(r.get("jcsa_ok"))
    unresolved = {r["seed"] for r in recs if r["stratum"] == "nonterm"
                  and not r["result"].get("ok") and not r["result"].get("unreachable")}
    assert set(rescued) <= unresolved, "follow-up seed that is not an unresolved non-terminal sample"
    for r in recs:
        if r["stratum"] == "nonterm" and r["seed"] in rescued:
            r["result"] = dict(r["result"], ok=True, jcsa_ok=rescued[r["seed"]])
    sizes = {"nonterm": count(chu_setup("file", identify_royals=True), "file", colour=True).total,
             "term": count(chu_setup("file", identify_royals=True, terminal_only=True), "file", colour=True).total}
    print(f"follow-up rescues {len(rescued)} of {len(unresolved)} unresolved non-terminal samples"
          f" ({sum(rescued.values())} also under JCSA)")
    registered_brackets(recs, sizes)


if __name__ == "__main__":
    main()
