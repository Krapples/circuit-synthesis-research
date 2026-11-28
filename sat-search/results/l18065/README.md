# L18065 sweep diagnosis and bounded replay

Sol reviewed the encoding and ran the comparisons. Luna traced the
original control flow and reviewed the essential-input bound. This is
research mode. The sweep uses complete bipartite edge functions, exact
fan-in-two AND/OR gates with distinct earlier operands, last-gate output,
and a live output cone. The owned variant additionally requires every
AND to be false whenever the target is false.

## Diagnosis

The recovered Claude scratch source used 20 processes and flushed one
line per completed graph. A graph first searched for an owned circuit
over successive budgets and then tested plain AO2 at the preceding
budget. Its 600-second check ran after the blocking SAT call returned a
candidate and the next counterexample row had been added. It therefore
could not stop a SAT call while the call was active. The other executable
named in the original launch command was not the backend: this sweep
used in-process PySAT CaDiCaL 1.9.5.

The archived [sweep](../../logs/l18065/sweep34.log) has 10 completed
graphs out of 21 listed. The three 8-gate plain checks had combined
per-graph times of 287.1, 368.8, and 494.2 seconds. The 10 archived
owned witnesses passed independent full-input and ownership checks.
The archived UNSAT rows are solver verdicts. The other 11 graphs
cannot be classified from this log.

The shared [graph-search review](https://chatgpt.com/share/6b0a3515-a338-83e8-b4ed-b96ef369adc6)
documents Windows timeout cleanup problems and examples where lower
conflict counts did not yield lower CPU time. The shared
[workflow review](https://chatgpt.com/share/6b0a3576-ce2c-83e8-b466-e7cda46f4ed8)
supports capped initial probes and selective extension. Neither shared
chat identifies the original sweep.

## Replacement

The [driver](../../experiments/l18065_sweep.py) emits JSONL case starts,
budget and phase transitions, parent heartbeats, per-budget results and
termination reasons through the [shared worker supervisor](../../workflow/supervise.py).
Heartbeat counters are the last worker snapshot
before a solver call, so they will stay fixed during that call. The
parent enforces a wall limit per graph and terminates only the worker it
created for that graph. The optional solver conflict budget is per gate
budget and can overshoot slightly inside CaDiCaL. Both limit outcomes
leave the queried gate budget open.

The [encoder](../../experiments/l18065_synth.py) keeps legacy CEGAR as
the default. Each vertex is essential because it has a matching
partner. If there are (k) binary gates and (2m) inputs in a live
output cone, its connected underlying graph has (k+2m) vertices and
at most (2k) edges, giving the owned search's starting budget
(2m-1). A direct OR of edge ANDs supplies the owned upper bound
(2|E|-1).

The opt-in `--rows frontier` loads edge minterms and maximal independent
sets. By monotonicity, every true input contains an edge minterm and
every false input is contained in a maximal independent set. An AND's
output is also monotone, so the maximal independent sets suffice for the
ownership constraint. The solver still checks each SAT witness on
every assignment. The independent set-based checker verified the
frontiers against all 4,416 assignments across the 21 sweep graphs.
The shared [truth-table helper](../../experiments/monotone_frontier.py)
also passed an exhaustive check of all 31 monotone tables through three
inputs and rejected every nonmonotone table in that range.

## Matched screen

Python 3.15.2, python-sat 1.9.dev25, CaDiCaL 1.9.5, one graph worker
at a time. The initial [manifest](triage.json) set a 20-second graph
wall limit and 25,000 conflicts per budget. All six fixed-budget runs
were conflict-limited. Encoding took 0.03–0.05 seconds and solver time
0.90–1.25 seconds. Frontier used one SAT call per case, and legacy used
12–14 calls. This screen localized the cost to solving and established
no new exclusions.

The [wall-only manifest](triage-wall.json) kept the 20-second wall cap
and removed the conflict cap for two pairs:

| Graph case | Plain gates | Legacy | Frontier |
| --- | ---: | --- | --- |
| 6 | 7 | UNSAT, 4.395 s solve, 90,630 conflicts | UNSAT, 2.333 s solve, 48,197 conflicts |
| 8 | 8 | Wall limit, open | Wall limit, open |

The table shows one run per configuration. Neither UNSAT was certificate-checked.
Case 8 is open for this replay; the archived completed run already
reported a solver UNSAT at this scope. After the screen, the parent
was changed to retain the latest round snapshot while throttling
printed events. Smoke checks then covered two simultaneous owned/plain
cases, an active-solver wall stop, and a conflict-limit exit.
The first two batches in [the result records](triage-results.jsonl)
precede that reporting change.
The extracted supervisor also passed a non-SAT smoke check covering
normal return, heartbeat, a wall-limited worker, and a worker exception
in one run. The first Windows smoke check exposed a broken pipe on
worker exit. Handling that close in the parent fixed the failure.
After extraction, the matched case-6 pair reproduced both verdicts and
conflict counts. Legacy and frontier solve times were 4.226 and 2.346
seconds, respectively.
The complete local runner logs are under
`.research/batches/1795831710071465200-51588/` and
`.research/batches/1795831786845680500-50244/`. The post-extraction
recheck is under `.research/batches/1795832262914106100-45232/`. Each
jobs file points to the per-attempt stdout and stderr.

From the repository root:

```powershell
python -B sat-search/results/l18065/verify.py --legacy-log sat-search/logs/l18065/sweep34.log
python -B sat-search/experiments/l18065_sweep.py 3 4 --list
python -B sat-search/experiments/l18065_sweep.py 3 4 --case 8 --plain-budget 8 --rows frontier --wall 20
python -B sat-search/workflow/research.py run sat-search/results/l18065/triage.json --workers 1 --memory-mib 1024
python -B sat-search/workflow/research.py run sat-search/results/l18065/triage-wall.json --workers 1 --memory-mib 1024
```

Case indices apply to the specified sizes. The next decision is whether
the [cofactor reader bounds](RESTRICTIONS.md) help on a wider set of complete
monotone functions and synthesis budgets. The present sample supports keeping
frontier rows and reader bounds opt-in.
