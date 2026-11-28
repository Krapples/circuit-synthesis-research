# Rank and certificate preflight for complete AO2 synthesis

Sol ran the screens and checked the witnesses. Luna reviewed reuse of the
existing [rank checker](../../experiments/certificate_rank.py) and the prior
replay evidence. All targets are complete monotone functions. Count only
two-input AND and OR gates, with no negations. The graph witnesses also
satisfy the sweep's ownership condition on every false row.

## Three short iterations

1. **Test rank before allocating the full SAT instance.** The rank bound
   excluded nine of the 21 budgets immediately below the size of a
   constructive circuit. In particular, cases 7–9 at eight gates each
   took less than one millisecond inside the worker on the local rank
   smoke test. The broader use is any complete monotone target whose
   minterms and minimal zero certificates are available.
2. **Apply that bound to single-input cofactors.** The
   [matched manifest](rank-cofactor-screen.json) used one worker, five seconds
   per case, complete frontier rows and the same whole-function rank check
   for every run. The tested budgets survive the whole-function check.

   | Case and budget | Frontier | Read-once cofactor | Rank cofactor |
   | --- | --- | --- | --- |
   | 7 at 9 | SAT, 10,332 conflicts, 0.631 s | SAT, 3,976 conflicts, 0.206 s | SAT, 13,345 conflicts, 0.877 s |
   | 10 at 9 | Wall limit | Wall limit | Wall limit |
   | 19 at 10 | Wall limit | Wall limit | Wall limit |

   Times are solver time from one run each. The additional clauses were
   slower on the feasible control. The two harder runs remain open at that
   cap in the full gate-position encoding. The
   [result rows](rank-cofactor-results.jsonl) point to the local batch
   under `.research/batches/`.
3. **Test how the certificate intersections can share wires.** A budget
   of `k` gates for `r` essential inputs permits at most `k − r + 1`
   extra uses of wires. The
   [complete certificate decomposition](../../experiments/certificate_decomposition.py)
   enumerates possible counts of readers at repeated wires. It also
   constrains the region and terminal assignments using the actual
   certificates. The plain gate-position solver does not need to run if
   every permitted arrangement is ruled out. Cases 10 and 19, both
   wall-limited in iteration 2, were excluded in 0.066 and 0.132 seconds
   in the direct decomposition screen. Case 20 at eleven gates used
   excess four and took about 1.4 seconds in a separate probe. These are
   single worker measurements. The 500-conflict target is per pattern
   and the solver can overshoot during an internal search interval.

## Exact sweep minima

The [replay checker](verify_rank_preflight.py) constructs a circuit by
factoring one star at each left vertex, then OR-ing the stars. In this
corpus each vertex is incident to an edge. The construction uses
`|E| + m − 1` gates on an `m × m` graph, is checked on every assignment,
and is also a valid owned witness. For the lower bound, the replay applies
rank first at one gate below this witness. If that is insufficient, it
checks a fresh Glucose proof trace by reverse unit propagation for each
remaining encoded reader-count pattern. Rank-pruned patterns use the
paper bound. The [case records](rank-preflight-results.jsonl) include the
rank, excluded budget, witness size, and checked trace counts.
Rank sufficed for nine graphs. For the other twelve, the independent
checker accepted 44 traces with 12,091 checked proof steps. Witness checks
covered 4,416 assignments across the 21 graphs.
The decomposition argument and encoding are covered by the repository's
paper argument and regression tests. No Lean or axiom audit was run.

The L18065 sweep has three opt-in flags. `--root-rank` screens the whole
target. `--root-decomposition` also tries terminal decomposition through
excess three, with the existing wall limit around the graph worker.
When the preflight allows the budget or reaches its limit, the sweep
continues with ordinary synthesis. `--restrictions 1 --rank-cofactors`
uses rank in the cofactor reader caps. The excess-four corpus check is
available through the standalone replay.

```powershell
python -B sat-search/results/l18065/verify_rank_preflight.py
python -B sat-search/results/l18065/verify_restrictions.py
python -B sat-search/experiments/l18065_sweep.py 3 4 --case 10 --plain-budget 9 --rows frontier --root-decomposition --wall 5
python -B sat-search/workflow/research.py run sat-search/results/l18065/rank-cofactor-screen.json --workers 1 --memory-mib 1024
```
