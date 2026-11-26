# Single-reader guard dependencies and cylinder peeling

Date: 2026-11-26. Base [689d102](https://github.com/Krapples/circuit-synthesis-research/commit/689d1028363893e7f0c108817c5f2ed34043cc83). This round refines the gate-role ledger using semantic constraints on actual operand identities. Unlike the previous ingress count relaxation, the new reader bound strictly improves the ordinary single-restriction baseline on finite truth tables. It is at most linear (2n-1), is not a superlinear SAT bound, and has not been Lean verified. L-clb-036 remains open.

Native status: [RESEARCH_NOTES.md](../../RESEARCH_NOTES.md) at blob 40ab7e6fb8bbe2bec9761af622bdba74310b87b8 describes the earlier independently audited quadratic/cubic controls and the native coupled first-gate reader audit at [coupled_reader](../results/coupled_reader/README.md). The latter has a separate seven-gate proof for 0x07e1 and reports a stronger recursive regional baseline. Our comparisons below are against the explicitly defined ordinary single-restriction baseline, NOT that stronger native baseline or every known lower-bound method. No production solver changes.

## 1. Single-reader guard lemma

Work with a full-support n-primary Boolean function f, n>=2, in the free-phase signed AIG model: fan-in-two AND gates, complemented edges and constants free. Restrict to a minimum live AIG. Every input is read at least once. No live gate can compute a constant or equal a signed primary or an earlier signed signal: replacing the wire by that constant or literal and deleting the gate would make a smaller circuit. The argument also holds in any live circuit with no constant or primary-equivalent gate outputs. Count operand occurrences, not just distinct readers.

For input i write Z_i for the zero set of its Boolean derivative on the other n-1 inputs:

    Z_i = { y : f(x_i=0,y)=f(x_i=1,y) }.

If x_i occurs as a primary operand exactly once, its unique reader has the form

    R_i = (x_i XOR phase) AND H_i(y).

The other operand H_i is a possibly complemented literal of an earlier wire, independent of x_i: if a prior gate depended syntactically on x_i, there would already be a primary occurrence. The gate cannot read x_i twice. In a minimum circuit H_i is nonconstant (a constant guard would make the reader redundant or constant). Hence its zero set is nonempty. If H_i(y)=0, the entire remainder of the circuit sees no difference between the two x_i assignments, since the only direct occurrence of x_i is through R_i. Thus

    nonempty H_i^(-1)(0) subset Z_i.

In particular if Z_i is empty, x_i must be read at least twice. This is the familiar everywhere-sensitive input rule. The new observation is to use the structure of Z_i to constrain the *other operand* and then the order of multiple single readers.

## 2. Forced dependency graph and shared readers

If Z_i contains no two points differing only in coordinate j, then every possible nonconstant guard H_i must depend on j. Otherwise one false assignment of H_i extends to two points along j, both in Z_i, a contradiction. Equivalently the derivative active set projects surjectively to the coordinates other than i,j. Define the directed forced-dependency graph with arc i -> j in this case.

Let U be the set of exactly-once-read primaries of a minimum circuit. Each arc i -> j with i,j in U implies that either R_j is a strict ancestor of R_i or the two readers are the same gate. The reason is that H_i depends on j, and every syntactic path from j into that guard must pass through its unique reader, except when the guard itself is the primary j. The latter case means R_i=R_j. The shared gate case must not be ignored.

Two singly-read inputs i,j can share an AND gate only if f factors through a signed AND of those two bits: among the four pair cofactors (functions of every other input), there is one exceptional phase pair, and the other three cofactor truth functions are identical. Denote this necessary test by Pair(i,j). It is also sufficient for abstract functional factorization through that signed AND, not a claim that a particular circuit is minimal. When a pair shares a reader, the other operand of either input is just the other primary, so no forced arc from either to a third input (even outside U) is possible.

Consequently any actual U admits a partition into singleton and Pair-compatible two-element groups. Contract each group. There can be no directed cycle between distinct groups in the induced forced-dependency graph, because the original circuit is acyclic. A pair group must also pass the no-third-dependency rule. Inputs with empty Z_i are excluded from U. Enumerating all subsets U and such partitions is a finite exact oracle for this relaxation. Let u_cycle be the largest accepted cardinality. This upper bounds the true number of single-reader inputs; passing does not guarantee circuit realizability.

## 3. Stronger guard-cylinder peeling

Pairwise arcs only test whether the derivative zero set contains a one-dimensional coordinate cylinder. A whole group of singly read inputs imposes a simultaneous higher-dimensional constraint.

Define Peel(U) recursively, with Peel(empty)=true. Reject any U containing an input with Z_i empty. For nonempty U, accept iff at least one of the following holds:

- There exists i in U such that Z_i contains a nonempty full coordinate subcube free in every coordinate of U minus {i}, with all other coordinates fixed, and Peel(U minus {i}) holds.
- There is a pair i,j in U passing Pair(i,j) and Peel(U minus {i,j}) holds.

**Necessity theorem.** Every subset of singly read primary inputs of a minimum AIG passes Peel.

Proof: induct on |U|. Choose a reader gate earliest in topological order among the readers of U. If it contains two U primary operands, remove this shared pair; Pair holds by the previous lemma. Otherwise let i be its unique U primary operand. Its other operand is independent of every input j in U minus {i}: if it were such a primary the gate would be shared; if a computed guard depended on j, the unique reader of j would be strictly earlier. The guard is also independent of i. Since it is nonconstant, it has some zero assignment on the coordinates outside U. Fixing those outside coordinates and allowing all other U bits to vary gives a full derivative-zero cylinder in Z_i. Remove i. The induction applies to the remaining subset of singly read inputs, even though removed inputs are no longer included in U. No actual circuit modification, change of reader identities or assumption of independence between guard functions is used. This proves the claim.

Peel is at least as strong as the forced-arc relaxation. Each successful peeling order yields the required singleton/pair partition. A singleton at its removal time has a cylinder free in all remaining inputs, so it cannot have a forced arc to a still remaining distinct group. For a Pair-compatible shared pair, the signed AND factorization ensures each input's derivative is zero on the entire opposite phase of its partner, so neither has forced arcs to outside the pair. The contracted graph is therefore acyclic.

Define u_peel=max{|U|: Peel(U)}. Then u_peel<=u_cycle and actual single-read count <=u_peel. The test keeps whole zero cylinders, not just independent pairwise dependencies or gate-output role rank.

Computational note: for a fixed U, peeling can be done greedily. The accepted subsets are downward closed: restrict a valid removal order; cylinders remain valid when fewer variables are required to be free. If a pair loses one member, the remaining singleton can be removed using the derivative-zero cylinder with the missing partner fixed to its blocking phase, which is free in all still remaining variables. Therefore removing any currently eligible singleton/pair from a feasible U leaves a feasible subset, and removing it from an infeasible U cannot lead to acceptance (otherwise prepend that removal). A stalled nonempty set is a certificate of infeasibility for the tested set. To maximize accepted cardinality the reference enumerates all subsets and memoizes the recurrence, rather than claiming a polynomial-time optimization. Full truth-table input already costs 2^n bits. No efficient algorithm for a succinctly encoded SAT predicate is asserted.

## 4. Distinct-gate consequence

For any live signed binary AIG with s gates and n essential primaries, there are 2s total gate-operand occurrences. Every internal gate except the output gate has at least one occurrence into a later live gate, so at least s-1 internal occurrences. If at most u primaries are singly read, there are at least 2n-u primary occurrences. Thus

    2s >= (s-1) + (2n-u),
    s >= 2n-u-1.

In particular

    C_AIG(f) >= 2n-u_peel-1 >= 2n-u_cycle-1.

The right-hand side ranges from n-1 to 2n-1. This is a genuine distinct-gate lower bound (charges operand occurrences only once), but by itself cannot exceed linear size. In comparison, the previous ingress count relaxation permitted every input to enter once, without keeping the semantic constraints on the other operands. The new bound excludes those abstract profiles when their reader ordering cannot realize the derivative zero sets.

Take the maximum of this bound with independent restriction, regional or other certified bounds. Do NOT add overlapping charges without a proof. A fixed topology that has a particular single-reader set U can be rejected if Peel(U) fails, even when the overall numerical bound is weak. This is a prospective synthesis filter requiring native differential testing before promotion.

### Example: XOR of a bit with three-input majority

Let f=x_3 XOR majority(x_0,x_1,x_2), truth table 0x17e8 with bit x_0 least significant in the assignment index. x_3 is everywhere sensitive, so it must be multiply read. For each majority variable i, its derivative zero set consists of assignments where the other two majority variables agree (and x_3 arbitrary). It contains no edge in either of those two variable directions. Thus the three majority inputs form a complete bidirectional forced-dependency graph. No pair passes the shared-reader test (the four pair cofactors cannot be reduced to one exceptional phase). At most one of the majority inputs can be singly read. We obtain C>=2*4-1-1=6.

The ordinary single-restriction baseline for this function is 5, using exact cofactor costs. For example fixing x_3 leaves majority3 of size four, and fixing a majority input leaves x_3 XOR a two-bit AND or OR, also size four. All smaller restrictions give at most 5 after the fixed-input charge. A seven-gate upper bound follows by computing majority3 with four gates then XORing with x_3 using three. We do not claim the exact four-input minimum or novelty of the six-gate lower bound relative to other known techniques.

### Example showing higher-dimensional cylinders matter

For majority on n=2m+1 inputs, m>=2, the derivative in i is one exactly when the other 2m bits have weight m. The derivative-zero set contains edges in every other coordinate direction, so no forced pairwise arc occurs. It has no coordinate subcube free in m or more positions: for any fixed outside weight, the possible total weights on a free set of size at least m include m. It does have a zero cylinder on m-1 free coordinates, by fixing the outside bits all zero. No pair passes Pair(i,j): the 00, mixed, and 11 pair cofactors are distinct (thresholds m+1,m,m-1 on the other 2m-1 variables). Thus a U of size m+1 cannot start peeling; any U of size <=m can peel by singletons. The relaxation gives u_peel=m and C>=3m+1=(3n-1)/2, versus the n-1 source-count or forced-arc bound. This is not asserted to improve the best known majority circuit lower bound. It demonstrates that the higher-dimensional dependency test is genuinely stronger at arbitrary n, not just four-input examples.

## 5. Executed finite replay

Run in this directory:

    node guard_dependency_check.js

The checker exhaustively computes signed AIG minima for every one-, two- and three-input function. It enumerates available-function sets in complement classes, starting with primary functions and free constants, extending by one AND of any two signed available distinct classes if the new class was not present. A duplicate class or constant is redundant in a minimum circuit, so this is complete for small costs. All 256 three-input functions are reached by size six; counts at sizes 0..6 are [8,24,64,30,104,8,18]. The final level needs only output reachability, not storing every size-six state. A preliminary attempt incorrectly assumed only parity remained at cap five; this was corrected by actually exploring the sixth level. The committed experiment uses exact cofactor minima.

For each of the 64,594 full-support four-input truth tables, compute the baseline B=max(n-1,max_(nonempty proper S,z) [C(f restricted to S by z)+n-|S|]), with the standard nonconstant restriction premise (constant demands dominated by n-1). The results are:

- Everywhere-sensitive inputs alone improve B on zero tables.
- Forced pairwise dependency graph with shared-reader groups improves B on 56 tables.
- Guard-cylinder peeling improves B on 520 tables.
- Peeling strengthens the pairwise-cycle bound on 46,128 tables (many remain below B).
- The pairwise-cycle bound improves the everywhere-sensitive-input-only charge on 35,952 tables.

First example improving B is 0x17e8: B=5, cycle=6, peel=6. First example where peeling improves the cycle bound is 0x0016: B=7, cycle=3, peel=4 (no improvement over B in this example).

Additionally sample 5,000 attempted random AIGs on three or four primaries (seed 870017). Keep only full-support outputs after skipping all gate outputs that are constants or primary-equivalent. There are 1,541 retained circuits. Traverse the live cone, count actual single-reader occurrences, verify both relaxations accept the true single-reader set, and verify the live gate count is at least the peeling bound. All assertions passed. Random circuits need not be minima; their normalization suffices for the necessity proof. [Replay](guard_dependency_replay.txt).

This experiment does NOT enumerate four-input minimum circuits, evaluate the stronger recursive regional baseline, measure synthesis runtime improvements, or test every previous packed asymptotic control explicitly. The theorem is universal for the stated signed AIG model, so the programmable router is not excluded: its additional reader occurrences are allowed. No paired SAT grammar or new Lean proof is required for this truth-table-level result.

## 6. Research interpretation and next tasks

The first gate-role ledger failed because it discarded paired operand behavior. This new lemma uses one concrete aspect of that behavior: a single occurrence of a primary has a nonconstant guard whose false assignments must be contained in the target's derivative zero set. Acyclicity forces all guards of earliest readers to ignore still unread single-read inputs. This is a context-sensitive capacity restriction with a sound actual gate charge, and it improves a standard finite baseline. However the charge only distinguishes one versus multiple input occurrences, so it saturates below 2n. It does not by itself advance the n^1.01 asymptotic threshold.

Next: (1) Independently audit the necessity/peeling and shared-reader proof, replay the exact small costs, compare against the native recursive regional and coupled-reader baselines; (2) if useful, incorporate the topology-sensitive test into a separate experimental checker, not production pruning before differential validation; (3) generalize from unique primary readers to small sets of readers with a common blocked context (joint guard patterns), including constraints on their shared intermediate signals. The latter may require accounting for actual reader cones and avoiding double counting. A potential stronger formulation is to bound the number of independent constraints forced on a common guard, with guard sharing explicitly handled. No such stronger bound is claimed here. For asymptotic SAT, one must show a charge growing beyond a constant number of primary occurrences per input or another genuinely superlinear distinct-gate invariant. Reuse native checked restriction and gate deletion lemmas. No novelty claim relative to classical gate elimination or existing reader techniques; L-clb-036 remains open.
