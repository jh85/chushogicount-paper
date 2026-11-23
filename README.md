# Chu shogi counting code

Exact candidate counting, Rank/Unrank and sampling (`src/count`), proof-game
planning, certification and statistical analysis (`src/plan`), JCSA move rules
and checkmate-ending analysis (`src/jcsa`), reduced-game validation
(`src/variant`), and an independent Lean counting/indexing project (`lean`).
Git tracks the code and experiment settings. Versioned release assets supply the
evidence for the final November JCSA estimate.

## Final JCSA over-the-board estimate (November 2026)

Including checkmate and capture of the last royal, the estimate is **3.87 × 10¹⁶⁴
reachable positions with either side to move**. The simultaneous intervals are
**[3.86576, 3.87110] × 10¹⁶⁴** for either side and **[1.93288, 1.93555] × 10¹⁶⁴**
for Black to move. Only the either-side interval supports three significant digits.

From a clean checkout, run the following command (Python 3.12+, standard library).
It downloads and checks the tagged evidence, verifies the 384,000 full draws and
four million screen decisions, and reproduces all five registered count intervals.

```sh
python3 scripts/verify_jcsa.py
```

[Methods, sample results and optional proof-game replay](docs/jcsa-20261122.md) ·
[Cite this release](https://github.com/jh85/chushogicount-paper/releases/tag/jcsa-otb-20261122)

## Setup and checks

Use CPython 3.14 for historical planner/set-order compatibility, a C++17 compiler,
make and Git. Counting/statistics use only Python's standard library (3.12+
for the counting baseline). Optional board PNG rendering needs Pillow >= 10.1;
Japanese labels also need a CJK font. Network access is needed for initial setup.

```sh
make                       # fetch/check engine pin; build programs and fixtures
make test                  # bounded counting, sampler, JCSA and variant checks
python3 src/count/candidates.py --all --exact
python3 src/plan/allcp_bracket.py
```

The public engine is fetched into ignored `out/engine` at v0.2.1, verified against
commit `1a941d5a7460bdc01de253eb3e5b80a598d1eb1a`. No private repository is needed.
`CHU_ENGINE`, `CHU_ENGINE_JCSA` and `CHU_PLAN` optionally override executable paths.
Programs, generated fixtures/tables, figures, records and certificates go under
ignored `out/`. Keep any explicitly supplied output paths there as well.

### Lishogi counter-strike correction

`make test-sakishishi` builds corrected engine commit `ea6f874` in a separate
checkout and checks the 31 rule cases. In C05 and C05b both rule sets forbid a
soaring eagle from taking the protected lion on the first step. In C05c the
lion is unprotected, so lishogi forbids the capture and JCSA permits it.
The original sampling engine, v0.2.1, already enforced the JCSA mid-step rule.
The corrected lishogi flag classes have the same weights, since every first-step
lion capture also has a direct capture on that square. In the separate historical
lishogi main-run audit, all 6,602 replies to active flags in the 503,180 archived
games were legal single moves. The November JCSA estimate uses its own samples.
[Engine correction and test cases](https://github.com/jh85/chushogi/commit/ea6f874e5cad3ba8ccaf08bd2268a0f4e5a5481d)

## Historical October experiments and outputs

October's JCSA move-rule comparison ended by royal capture. Its separate G13/G13b
checkmate analysis bounded the full Black-to-move count at [1.87418, 1.94215] × 10¹⁶⁴.
The November study directly sampled the flag and terminal contributions and supersedes
that preliminary full interval. The October lishogi estimate and royal-capture
comparison have their own targets.

`experiments.json` retains the October main/earlier run settings, static-sample seeds,
D13 pilot/run/re-analysis settings, follow-ups and Bayesian settings. For example:

```sh
python3 scripts/experiment.py mf --print  # inspect without running
python3 scripts/experiment.py flags       # static sample: seed 171, 10^8 draws
python3 scripts/experiment.py lanes       # I10 sample: seed 173, 10^7 draws
python3 scripts/experiment.py mf          # main run: seed 192, 504,000 samples
```

Use `out/variant/bfs V1 --depth 2` for a bounded example; omit the depth limit
only for an intended full campaign. Inspect other named configurations with
`--print`. For D13 use `g13`, then `g13b-seeds`, then `g13b`; these consume M-F's
records. The P2/P3 configurations preserve their sample offsets and rule reading.

After generating records, the analysis and output commands include:

```sh
python3 src/plan/strict_bracket.py --records out/runs/mf.jsonl --flags out/runs/flags-seed171.log --lanes out/runs/lanes-seed173.log
python3 src/jcsa/d13_bracket.py out/runs/g13.jsonl --override out/runs/g13b.jsonl
python3 scripts/experiment.py mf-certificates
python3 scripts/experiment.py mf-replay
python3 src/count/fig1.py out/figures/fig1
python3 src/plan/fig2.py out/runs/mf.jsonl out/figures/.main
```

`allcp_bracket.py` evaluates the paper's fixed sufficient statistics; it does not
redraw samples or load historical records. The estimator also retains the
paper's fixed static calibration inputs. Registered/strict normal-input bounds
are nominal; the supplementary Clopper–Pearson-only construction is distinct.
These are current source algorithms with recorded run settings, not a promise
of byte-identical historical reruns. The original October code snapshots and per-game evidence
remain outside this repository. Record-based tests require explicit generated
records/certificates; use each program's `--help` for those options.

## Lean

Install elan/lake and the pinned toolchain; Mathlib and all transitive revisions
are locked in `lean/lake-manifest.json` (Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`, Lean 4.35.0).

```sh
elan toolchain install leanprover/lean4:v4.35.0
make -C lean setup          # fetch locked dependencies and Mathlib cache
make -C lean check          # bounded specification/ordinary-file checks
make -C lean audit          # full proof build and axiom audits
make -C lean counter        # execute the exact counter
make -C lean certificate    # separate native numerical certification
make -C lean examples       # six deterministic Board rank/unrank examples
```

The split local-game witness files are proof source required by imports, not
sampling certificates. Their optional Python generators write proposed
replacements to `out/lean-witnesses` when run from this repository's root.

Lean independently defines canonical Boards satisfying I1–I9, with strengthened
I5, and proves counting/indexing results. It merges promoted kirin/lion,
phoenix/free king and crown prince/king; other promoted roles remain distinct.
`C_r`/`C_nr` partition by Black royal presence, not all terminal conditions.
Boards omit side-to-move and flags; White must have a royal. I10 is outside this
candidate definition. Main proofs use standard Lean axioms; the isolated
`native_decide` certificate additionally trusts compiler/runtime/native execution.
Uniformity assumes a uniform integer input. These results do not verify Python
execution, RNG correctness, full-game reachability or Monte Carlo coverage, and
do not expand the manuscript's claims.

The October code came from counting project `e25a3b103bde184a37c9bf81b95ef7e5fa3db19b`
(clean tracked sources); the accompanying Lean project was untracked and is
preserved here as proof source. The November production source and engine identifiers are recorded in the
release freeze manifest. See
[THIRD_PARTY.md](THIRD_PARTY.md) for provenance, dependency notices and the
separate licensing clarification needed for the pinned Chushogi snapshot.

## License and provenance

The original code here, including the original Lean sources, is licensed under
[Apache License 2.0](LICENSE). Existing third-party terms and notices remain
applicable to their respective material; this grant does not replace them.

Chushogi is the author's own engine repository, fetched separately for setup.
Lishogi/scalashogi was consulted to interpret ambiguous rules; the author
confirms that no Lishogi source code was incorporated. The pinned engine
separately credits external test fixtures. See [THIRD_PARTY.md](THIRD_PARTY.md)
for those fixtures and the CPython/MT19937 compatibility notices. This project's
license does not automatically license the separately fetched engine snapshot.
