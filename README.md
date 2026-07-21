# WOWII Hamiltonian-path conjecture sweep — reproducibility package

Refutation campaign for Written on the Wall II (Graffiti.pc) conjectures
189, 194, 199, 200, 209, 213, 217. See the companion Lean certificates:
- #200: branch `proof/wowii200-counterexample` (pinned 9dd290db…)
- #209: branch `proof/wowii209-counterexample` (pinned 57801283…)

## Contents
- `wowsweep.c` — search engine: decides traceability (greedy + exact
  subset-DP fallback), then evaluates all seven conjecture premises in exact
  integer arithmetic on non-traceable survivors. `-T` runs self-tests, `-D`
  dumps all invariants per input graph.
- `run_sweep.sh` — exact commands used (geng -cq, 12-way res/mod split for
  n = 10, 11).
- `crosscheck.py` — validation against independent implementations
  (brute-force traceability, networkx node_connectivity,
  SpanningTreeIterator, brute-force independence/domination) on random
  connected graphs: 219 of 300 G(7, p) samples were connected and all 11
  invariants agreed on every one.
- `results/` — every hit (`<conj> <graph6> leaves=<k> twoconn=<0|1>`) and
  per-run totals. Totals match OEIS A001349 exactly:
  11,989,760 connected graphs for 4 ≤ n ≤ 10 (247,883 non-traceable) and
  1,006,700,565 for n = 11 (6,469,055 non-traceable).
- `VERSIONS.txt`, `SHA256SUMS`, `sweep.log`.

## Headline results
- #200: unique counterexample on n ≤ 11: `J??FFBRq}N_` (11 vertices).
- #209: unique counterexample on n ≤ 11: `J?o}]^Nr}^_` (11 vertices).
- #189 (inclusive dist_even), 194, 199, 213, 217: no counterexample, n ≤ 11.
- Repaired #200 (≤ 2 leaves / 2-connected): no counterexample, n ≤ 11.
- `189B` hits in results/ are the *excluding-v* misreading of dist_even —
  refuted by the 4-vertex claw, hence not the intended reading.

These are computational results, not Lean-certified ones; independent reruns
are welcome. Reproduce with: `cc -O2 -march=native -o wowsweep wowsweep.c &&
./run_sweep.sh` (~10 min on 12 cores for n = 11).
