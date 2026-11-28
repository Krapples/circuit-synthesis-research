# Comparator-05 solver profiling

**Date:** 2026-11-27

**Task:** L18065, research mode

**Scope:** Complete monotone comparator-05 truth table on 8 inputs; binary AND/OR gate budget 14.

**Roles:** Sol led the analysis and implementation; Luna reviewed the CLI and profiling paths read-only.

## Question and result

The 14-gate decomposition query remains **open**. Root bounds give rank 11 and color bound 14, leaving excess 7. The certificate matrix has 550 cells. Of 64 reader-count patterns, 63 are rejected by rank/capacity filtering and the only encoded pattern is seven two-reader gates.

Stage profiles locate the delay in SAT search. With cached cofactor evidence, the target-bound cache load takes under 1 ms, Python formula construction takes 0.31–0.37 s, and solver initialization takes 0.34–0.40 s. A 3 s MapleChrono call returns at about 3.01–3.02 s with `UNKNOWN`. A Glucose4 call can take 6.59 s for the same 3 s timer, because this instance responds slowly to interruption. No run here certifies UNSAT or finds a 14-gate witness.

## Matched measurements

All rows use the same target, budget, cached cofactor cuts, static coexistence clauses, closed-set cuts, one surviving reader pattern, 1,000 requested conflicts, and a 3 s per-call timer unless specified. Peak memory is the process high-water mark. A timer-limited `UNKNOWN` is not evidence of infeasibility.

| Configuration | CNF variables / clauses | Encode | Solver start | SAT call | Solver counters | Result |
| --- | ---: | ---: | ---: | ---: | --- | --- |
| MapleChrono, no provider/port constraints | 76,995 / 234,992 | 0.310 s | 0.341 s | 3.013 s; 3 ms interrupt lag | 1,831 conflicts; 218,115 decisions; 9.34M propagations | UNKNOWN |
| MapleChrono, provider ancestry plus exact capacity prescreen | 77,379 / 239,562 | 0.317 s | 0.353 s | 3.023 s; 17 ms interrupt lag | 1,316 conflicts; 137,029 decisions; 8.15M propagations | UNKNOWN |
| MapleChrono, second provider-ancestry run | 77,379 / 239,562 | 0.365 s | 0.400 s | 3.016 s; 2 ms interrupt lag | 1,597 conflicts; 190,546 decisions; 9.24M propagations | UNKNOWN |
| Glucose4, provider ancestry plus exact capacity prescreen | 77,379 / 239,562 | 0.319 s | 0.360 s | 6.593 s; 3.584 s interrupt lag | 5,060 conflicts; 8,111 decisions; 38.48M propagations | UNKNOWN |

The two Maple provider runs are not repeated enough to support a speedup claim. They show no decisive change in elapsed search time. The provider ancestry adds 384 variables and 4,570 clauses; encoding those constraints takes about 5–7 ms. The capacity prescreen takes 2–6 ms, checks 14 layouts, finds zero obstructions, and adds zero clauses on this target.

An exact port constraint ablation added 270 clauses. Its Glucose4 call also ended UNKNOWN; that run returned after 6.889 s with 3,334 conflicts and a 3.884 s interrupt lag. This is not a useful improvement signal. Keep the port and provider restrictions opt-in.

## Lazy aggregate mode

Sol added an opt-in `--no-local-intersection` flag under `--lazy`. It preserves the existing default and rejects static coexistence and cofactor clauses that assume local intersections. This makes the model-level provider and capacity cuts reachable from the CLI.

| Target | Formula | Encode / solver init | SAT call | Counters and cuts | Result |
| --- | ---: | ---: | ---: | --- | --- |
| Comparator-05, 3 s cap | 251,835 variables / 532,599 clauses | 0.521 / 1.034 s | 3.025 s | 156,428 decisions; 5.23M propagations; no model, so no provider/capacity cuts | UNKNOWN |
| Comparator-05, 8 s cap | 251,835 / 532,599 | 0.573 / 0.960 s | 8.007 s | 3,325 conflicts; 982,009 decisions; 18.54M propagations; no model, so no provider/capacity cuts | UNKNOWN |
| Hypergraph-21, budget 8, 3 s cap | 4,791 / 10,669 | 0.012 / 0.018 s | 3.015 s | 27,466 conflicts; 438,877 decisions; 8.67M propagations; no model, so no cuts | UNKNOWN |

For comparator-05, aggregate mode is about 2.2 times the clauses and 3.3 times the variables of the local-intersection formula. It reached no relaxed model even after 8 s, so it never invoked the model-level cuts. The known 8-gate hypergraph control also failed to return a candidate in 3 s; the local-intersection run found and checked one in under 0.1 s. The exposed mode is useful for future profiling but is a poor path for these two cases. The existing provider and capacity tests exercise the cut code directly; no target run here exercised those cuts.

## What the profiles revealed

- **SAT search is the critical path.** The solver call is about an order of magnitude longer than formula construction. `cProfile` attributes 3.02 s to the MapleChrono solve call. The 3 s timer is responsive on MapleChrono but not on Glucose4 for this formula.
- **Conflict limits are not wall limits.** A CaDiCaL call with a 10,000-conflict request took 25.5 s inside the solver (26.7 s end to end); a separate 1,000-conflict CaDiCaL run returned at 1,005 conflicts in 2.90 s. The MapleChrono aggregate-mode control reported 27,466 conflicts after a 1,000-conflict request, in 3.01 s. The earlier Glucose4 run did not return before its external wall cap. Keep an independent process wall limit around every long solver run.
- **A cached cofactor artifact avoids repeated work.** Recomputing the prefix screen took about 1.48 s in the prior run; loading the target-fingerprinted artifact took 0.6–0.8 ms and supplied 39 exclusions from 12 checked subproblems plus 3 derived cases. The loader checks target fingerprint, budget, schema, and mask shape. It does not replay each subproblem proof at load time; trust in those cuts still rests on the checked-in generated artifact and its reviewed provenance.
- **Provider levels are currently indistinguishable in local-intersection mode.** That path adds the same static provider-ancestry clauses for `eligibility`, `matching`, and `exact`; the level-specific model-cut routine runs only with local intersections off. The new flag reaches that routine, but these timed target runs produced no relaxed model, so no speedup or model-cut benefit is established.
- **The profiler initially cost 0.24 s.** `cProfile` showed three `peak_bytes()` calls spending about 0.24 s in Windows platform discovery/WMI. Switching the OS branch to `os.name` reduced the three samples to about 0.026 s in the next run, saving roughly 0.22 s of profiler overhead.
- **The run wrapper needs both decomposition guards.** Two early profiling attempts used the default `--max-excess 6` and `--max-cells 400`; the target needs 7 and 550. Those attempts fell through to full synthesis, which ignored the per-call timer and reached the outer wall cap. Use `--max-excess 7 --max-cells 600 --preflight-only` for this query.

## Reproduction

Run from the repository root. The outer `--wall` is enforced by the process supervisor; `--solve-seconds` is only the limit for an individual SAT call.

```powershell
python -B sat-search/results/l18065/compare_complete.py comparator-05 14 `
  --preflight --preflight-only --max-excess 7 --max-cells 600 `
  --lazy --static-coexistence --prefix-oracle --closed-sets `
  --prefix-evidence sat-search/results/l18065/singleton-prefix-cofactors.json `
  --conflicts 1000 --solve-seconds 3 --solver maplechrono --wall 15 `
  --profile-jsonl sat-search/logs/l18065/profile-comparator05.jsonl `
  --cprofile sat-search/logs/l18065/profile-comparator05.pstats
```

Detailed per-stage JSONL, cProfile dumps, wrapper heartbeats, and full stdout logs remain in `sat-search/logs/l18065/`. The summary manifest is [profile-comparator05.json](profile-comparator05.json).

## Verification and next action

Python compilation passed. The cofactor crossing check matched 12,096 encodings; rank checks passed 10 tests and checked 360 cones; lazy-certificate checks passed 4 tests and checked 1,800 compatibility queries. Provider checks passed 5 tests with 240 independent provider-table comparisons; capacity checks passed 7 tests, including 400 global-oracle comparisons. CLI checks rejected aggregate mode without `--lazy` and rejected local-only cofactor flags in aggregate mode. The target solver result remains `UNKNOWN`; no Lean or axiom audit was run.

Next, stop spending comparator-05 runs on aggregate mode unless a stronger reason predicts a quick model. Focus on a topology or branching restriction compatible with local intersections, and use the existing small tests before exposing it in the solver. Keep provider ancestry and port constraints disabled by default until repeated matched runs demonstrate a benefit.
