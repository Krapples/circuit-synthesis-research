# Fully genuine fork mode CNFs

The fork-kernel reduction in the handoff remains exact. Each deficient tree of the matching
background needs one extra option. A mode clause lists the fork choices that can supply that
option. A satisfying mode assignment serves all deficient trees simultaneously because each
fork leaf can serve its own component, and the two leaves do not conflict. The second
contraction folds a dominating mode into private options and a two-choice mode into a shared
edge. The stated free-complement AIG bound is
`O(N log^5(N+2) + p 2^p)` when `p` bounds the number of genuine forks after the first
contraction for every input under consideration. This uses the handoff's dynamic
matching-background circuit construction. The replay builds only the compressed-core AIG.

## A reduction that survives both contractions

Every width-at-most-three CNF with `L` literal occurrences and no empty clause has a
linear-size, parsimonious reduction to a mode CNF with the following properties.

- Every variable has exactly one positive and two negative occurrences in distinct clauses.
- Every clause has width two or three, with distinct variables. Any two clauses share at
  most one variable.
- The mode CNF is the unchanged result of both matching contractions and the dominated-mode
  check, and it has no pure literals or unit clauses.

First replace a unit `(ℓ)` with the binary clauses `(ℓ ∨ z)`, `(ℓ ∨ ¬z)`, and
`(¬ℓ ∨ ¬z)` using a fresh `z`. They force `ℓ` true and `z` false, giving a unique extension
of every satisfying assignment. An input with an empty clause can be mapped to the reduction
of the four binary clauses on two variables with all choices of signs, which is unsatisfiable.

Make three replicas of each resulting clause. Introduce a variable copy for each replicated
literal occurrence and link the copies of each original variable by a directed cycle of
implications. Order the copies by original occurrence and then by replica number. Adjacent
copies, including the wraparound pair, have distinct replica numbers, and each cycle has
length at least three. A satisfying cycle has all copy values equal. Each copy has one positive
and one negative cycle occurrence, and one occurrence in a replicated clause. Complement
every copy whose replicated occurrence was positive, so that it becomes negative and the
cycle contributes the one positive occurrence. This coordinate change is bijective.

Replicated clauses have disjoint copy sets. Two link clauses share at most one copy, since
each consistency cycle has length at least three. Any link clause intersects any replicated
clause in at most one copy, since its endpoints have different replica numbers. If the
normalized CNF has `L′` literal occurrences, there are `3L′` copies and `9L′` output
literal slots; `L′ ≤ 6L` when there is no empty clause. Restricting a target model to one
decoded copy per variable recovers its unique source model.

Realize each variable by a `P3` fork whose center is the positive literal slot and whose
leaves are the negative slots. Use one group per clause and make every vertex available.
There are no background resources, so every group is a singleton deficient component of
the resource graph. Each fork sees three distinct deficient labels, hence is genuine. The
second contraction has no private or shared resources to contract. It returns the same
clauses up to label order. This proves NP-hardness for deciding feasibility when the fork
template is supplied as part of the instance, even on this class. It gives no deterministic
circuit lower bound for availability on a fixed template. In particular, the reduction
certifies one availability point per template.

For a source without empty clauses, its incidence graph is a minor of the output incidence
graph. Keep one replica of each normalized clause and contract each connected chain of
copy vertices and link-clause vertices into its source variable. To recover a source unit,
keep one of its three binary clauses and delete the fresh auxiliary and the other two
clauses. This preserves an edge for every source incidence. Consequently the local
restrictions do not bound incidence treewidth. For example, binary clauses indexed by edges
of a complete graph give incidence graphs containing that graph as a minor.

## When width alone suffices

If every residual clause has at least three distinct variables, the mode CNF is satisfiable.
Each variable occurs in at most three clauses. Every clause subset `S` sends at least
`3|S|` incidence edges to its neighboring variables and receives at most three per neighbor.
Hall's theorem gives a matching that assigns a unique variable to each clause. Setting each
matched variable to satisfy its own clause gives a satisfying assignment. More generally, for
clauses of widths two and three, a Hall-deficient subset with deficit
`δ = |S| - |N(S)| > 0` contains at least `3δ` binary clauses by the same edge count.
This identifies where distinct-variable matching can fail; satisfiability may still hold
through one variable serving multiple clauses. The reduction above retains binary links.

## Replay and evidence

Run from the repository root.

```powershell
python -B sat-search/results/fork_mode_core/handoff_reference.py
python -B sat-search/workflow/research.py run sat-search/results/fork_mode_core/manifest.json --workers 1 --memory-mib 128
```

The frozen handoff replay passed 26,260 semantic checks and 52,480 compressed-core AIG
evaluations. The new checker independently enumerated source assignments and target CNF
models, verified the model bijection, and recovered mode clauses from their fork slots.
It passed all 256 exhaustive two-variable cases, 400 seeded cases using at most six source
variables, and one empty-clause regression. The runner recorded 0.860 s for the new job,
with a 20 s cap and an estimated 128 MiB reservation. Peak memory was not measured. The
replays are finite evidence accompanying the paper arguments. No Lean check, exact
synthesis budget, or native filter was added.
