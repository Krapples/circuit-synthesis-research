# Deleted-point projective plane with a proxy wire

L-meta-2216 asks for a refutation via a fan-in-two monotone AND/OR circuit of at most 61 gates.
The circuit must compute the complete graph function on points `0..11` and lines `12..24`, with
an edge when `(point + line + 2) mod 13` belongs to `{0,1,3,9}`. A designated wire must compute
the disjunction of `S = {12,13,15,21}` on every input where the graph output is false.

## Construction and exact boundary

The 62-gate circuit uses 48 gates for twelve point stars, eleven OR gates to combine them, and
three OR gates for the proxy. The graph output is wire 83 and the proxy is wire 86. Lean 4.36.0
checked `PG3LocalAudit.localUpper62` in [Upper62.lean](Upper62.lean) on symbolic Boolean inputs.
The axiom report was `propext`, `Classical.choice`, and `Quot.sound`.
[The independent verifier](verify_exhaustive.py) checked all 33,554,432 inputs, including
29,854 on which the graph output is false. The proxy is true on 20,978 of those inputs. The
exhaustive check took 0.25–0.31 s in Python 3.15.2 on the development machine.

A monotone graph output is exact once it accepts all 48 edge masks and rejects all 553 maximal
independent sets. Every true mask contains an edge and every false mask extends to a maximal
independent set. The proxy must accept the four special singletons and reject the 197 maximal
independent sets in the graph induced after deleting `S`. A false graph mask containing a special
line dominates its singleton. A false graph mask omitting `S` extends to one of the 197 sets.
This provides a complete boundary of 601 graph labels and 201 proxy labels.
An upstream reduction for the opposite step records the same boundary sizes and 62-gate upper
bound. [Prior reduction](https://github.com/open-goat/pequalnp-proofs/pull/8694)

Adding the missing point with input `z` extends any such two-output circuit to the full plane
via `f OR (z AND w)`. When `f` is false, the new edges are exactly the ones detected by `z AND w`.
When `f` is true, the extension is already true. The line reindexing for the cyclic coordinate
`p + (line − 13)` is `line ↦ 13 + ((line + 2) mod 13)`. The checked unconditional 38-gate
lower bound for the full plane therefore gives a 36-gate lower bound for this two-output problem.
[Full-plane bound](https://github.com/open-goat/pequalnp-proofs/blob/d9f1ea23/lean/PEqualNP/Outside/L_meta_1484.lean)

## Single-level lower bound

Suppose each path from an input to the graph output uses at most one AND. Propagate constants
and aliases through both outputs, and retain gates with a live reader in either cone. This
preserves both outputs and only deletes gates. Each surviving AND in the graph
cone takes two pure disjunctions. Their supports are disjoint since the graph output is false on
each singleton. Their Cartesian product consists entirely of edges. Bipartiteness and the
absence of 4-cycles make the product a star. These stars cover all 48 edges. A matching with
twelve distinct lines is given by `(p + line + 2) mod 13 = 0`, so the star centers number at
least twelve.

For each center `c`, let `k_c` count its ANDs and let `d_c` count their distinct leaves. The
disjunction cones on those leaves have `k_c` designated roots and need at least `d_c − k_c`
binary ORs. This follows by counting connected components after forgetting edge directions.
Two centers cannot share a support of size at least two. Centers on opposite sides have leaf
sets on opposite sides, and two centers on the same side share at most one neighbor. Thus
these lower bounds add over centers. The top OR aggregation needs at least `sum(k_c) − 1`
gates. Since `sum(d_c) ≥ 48`, the graph cone needs at least `48 + 12 − 1 = 59` gates.

Now set every input outside `S` to zero. Each remaining point is adjacent to exactly one
line of `S`. Every graph-cone wire becomes zero or a projection of one special input. This
also holds for ORs on the center side and for wires above the ANDs. Computing the disjunction
of four essential inputs from these projections needs at least three additional gates outside
the graph cone. The construction therefore attains the minimum of 62 for this restriction.
The argument assumes the single-level property of the graph-output cone.

## Two-point isolated replacements

After constant and alias propagation, consider an isolated two-point module with the seven
lines touching the two selected points and
each special line. Other points are zero. Its graph is connected and is not a biclique.
The graph-output cone has at least one repeated read. A read-once OR root has a disconnected
quadratic graph, while a read-once AND root of a complete quadratic function forces every
prime implicant of each child to be a singleton, producing a biclique.

For a two-output live circuit with `n` essential inputs and `g` binary gates, count the two
output designations as readers. There are `g − n + 2` read occurrences beyond the first
reader at each input or gate. Count the surplus separately inside the graph cone, using
its own output designation. Every reader crossing from that cone to the proxy-only cone
or designating the proxy within the graph cone adds one occurrence to this surplus.

- If the two points meet at a special line, there are twelve essential inputs. The graph
  repeats at least one read and the proxy uses a crossing, giving `g ≥ 12`.
- If they meet at an ordinary line, there are eleven essential inputs. Two crossing readers
  already give `g ≥ 12` using the graph's repeated read. With a single crossing wire `t`,
  each of the two incident special lines must make `t` true on its singleton. Fixing one
  of those lines true, changing the other still changes the graph when the other line's
  point is active and every other point is false. Hence each special line has a path to
  the graph output bypassing `t`, as well as a path to `t`. They must first branch at
  distinct vertices. If both first branched at the same vertex, the two output bits together
  could take at most two values when the two lines vary with the other inputs fixed. With one
  incident point active they take at least `(0,0)`, `(0,1)`, and `(1,1)`. The two branch
  vertices occur before `t` and each contributes an extra read in the graph cone. Including
  the crossing yields `g ≥ 12`.

The isolated two-point baseline has nine graph gates and three proxy gates. The argument
does not factor a general shared circuit into isolated modules.

## Three points on one special line

For this orbit the module has sixteen essential inputs. Its graph has the common line `s`
and three private leaves at each point. The graph cone needs at least two surplus readers.
To see this, fix any proxy-only inputs to zero and propagate constants and aliases. These
operations cannot create a branch in a tree or turn one branch with two outgoing uses into
multiple branches. If the resulting graph cone had only one surplus reader, it would have
one wire `t` read twice. Every primary input in the cone of `t` enters the remaining graph
circuit through `t` alone.

For any proper subset of the graph inputs entering through one wire, each vertex with an
external neighbor must make the wire true on its internal singleton. Adding any internal edge
to such a singleton cannot change the wire, yet it changes the graph output with all external
inputs zero. Hence this subset is independent. Each of its vertices then has an external
neighbor and sets the wire true on its singleton. Varying the external singleton shows that
their neighborhoods coincide. The subset is proper because a normalized cone with every
input entering through `t` has output `t` by idempotence and does not need two readers of `t`.

In this graph the only sets of distinct vertices with identical neighborhoods are private
leaves of a single point. If the input set of `t` consists of those leaves, setting them all to
zero leaves an induced four-vertex path on the other two points, `s`, and one private leaf.
Its edge function cannot be read-once, but the remaining cone has no repeated wire. If the
input set of `t` is a different singleton, setting it to zero still leaves such a path, except
when the singleton is `s` itself.

For `t = s`, unfold the cone to a formula in which `s` appears twice and every other input
appears once. Setting `s = 0` leaves all other inputs essential. Each occurrence of `s` thus
attaches to the surviving formula via an OR: an AND attachment would delete essential leaves.
The surviving formula is a top OR over three disjoint point stars. This follows because a
read-once AND root for a quadratic function yields a connected biclique, and read-once ORs
partition the graph into connected components. An attachment above the stars would accept
the singleton `s`. An attachment within one star can create edges incident to only that
star's point. Two occurrences of `s` therefore cannot create its three incident edges.

Counting the two forced graph readers and one crossing to the proxy yields `g ≥ 17`. The
ordinary construction attains 17 for this isolated module. As with the two-point proof, the
count concerns the isolated topology and does not bound arbitrary global reuse.

## SAT records

All jobs used the repository `cube_search` topology and truth-clause builders with MapleChrono,
AND/OR gates, and 22 workers per pool. Wall limits are per job. `OPEN` indicates interruption
under the cap. The SAT exclusions are solver verdicts without separately checked certificates.

| Search | Scope | Cap | Verdicts |
| --- | --- | --- | --- |
| Isolated modules | All 29 orbits of 1–6 point subsets under 432 color-preserving automorphisms. Budget `5k+1` with `k` open stars. | 35 s | 1 UNSAT, 28 OPEN |
| Fixed-star windows | 22 layouts and seeds reserving 1–4 point stars. The suffix can read the original inputs and any fixed wire. | 45 s | 3 UNSAT, 19 OPEN |
| Final-OR windows | 22 layouts and seeds reserving 2–4 point stars, with a reserved final OR joining the fixed graph prefix and synthesized output. | 110 s | 22 OPEN |
| Canonical proxy windows | 22 layouts with a fixed three-OR proxy available as inputs to the synthesized graph suffix. | 105 s | 22 OPEN |
| Module controls | Seven one-to-three-point orbits, each searched with graph fanout rules and two row sets. Eight planted star controls check the encoder and output selection. | 60 s | 2 UNSAT, 12 OPEN, 8 planted SAT |

The six SAT exclusions concern one-point windows. Other 61-gate topologies with nested ANDs
remain open. The next search would need a tighter structural
restriction on the nested part or a construction exploiting a shared gate with a negative mask.

Run the Python commands from the repository root. Use the repository's configured PySAT and
NetworkX dependencies, or set `PYTHONPATH` to the local `.scratch-sat` directory as in these runs.
Give each SAT run a fresh output path. The corresponding JSONL files retain the parameters,
seeds, elapsed wall times, and solver verdicts.

```powershell
$probe = 'sat-search/results/pg3_deleted_point_proxy_2216'
python "$probe/verify_exhaustive.py"
python "$probe/pg3-proxy-sat.py" sat-search/logs/pg3-modules-replay.jsonl
python "$probe/pg3-window-sat.py" sat-search/logs/pg3-windows-replay.jsonl
python "$probe/pg3-final-or-sat.py" sat-search/logs/pg3-final-or-replay.jsonl
python "$probe/pg3-canonical-proxy-sat.py" sat-search/logs/pg3-proxy-replay.jsonl
python "$probe/pg3-module-controls.py" sat-search/logs/pg3-controls-replay.jsonl
```

Check `Upper62.lean` with Lean 4.36.0 in an environment where the pinned Mathlib and
`PEqualNP.Defs` are on `LEAN_PATH`. The proof uses the standard circuit wire semantics and
per-gate evaluation lemmas to keep symbolic reduction bounded.
