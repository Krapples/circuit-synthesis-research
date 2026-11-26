# Exact single-reader feasibility and a two-read AIG normal form

Date: 2026-11-26. Base [8b797db](https://github.com/Krapples/circuit-synthesis-research/commit/8b797db4eca0873dc7b2fa680d31b301a8778b57). Read [guard_dependency_handoff.md](guard_dependency_handoff.md) first. This round proves a converse to guard-cylinder peeling and a constant-factor two-primary-read normal form for unrestricted signed AIGs. It exposes a fundamental limitation of extending a primary-reader-only charge to higher multiplicities. It does not resolve L-clb-036, establish new asymptotic size lower bounds, or claim literature priority. No production solver or verified Lean library changes.

## 1. Exact scope and conventions

A signed AIG uses fan-in-two AND gates, free constants and complemented edges. Read count means primary operand occurrences in the live output cone, not the number of unfolded leaf occurrences or the fan-out of derived signals. A normalized circuit has no live AND computing a constant or a function equal up to complement to a primary or an earlier live gate. A minimum circuit has this property, but a normalized circuit need not be minimum. Semantic normalization is used for existence proofs, not asserted to be computationally cheap for arbitrary succinct circuits.

The earlier guard-cylinder necessity theorem applies to minimum AIGs, and indeed to normalized full-support AIGs: if U is a subset of singly read primaries, choose the earliest reader among U. Either it combines a pair i,j, with three equal pair cofactors and one exceptional phase, or its other operand is a nonconstant guard independent of every remaining U variable. The derivative-zero set of i then contains a cylinder free in U minus {i}. Recursively remove a singleton or a compatible pair. See the previous proof for exact definitions.

## 2. Converse: peeling is exact for existence with no size bound

**Theorem.** For a full-support Boolean f on n>=2 inputs and a specified subset U, Peel(U) holds iff there exists a normalized signed AIG for f in which every member of U has exactly one primary operand occurrence. This is a statement about a specified subset, not about exactly which other inputs have one occurrence. No bound on the constructed circuit size comparable to the minimum is asserted. In particular this does not make the previous numerical lower bound tight.

Necessity was proved previously. For sufficiency choose a successful peeling order, grouping inputs as singletons or pairs. Let Y be all variables outside U. Build a circuit that uses Y freely and processes the groups in that order. Its state is the vector of original Y bits and the outputs of the already processed reader gates. Maintain the following invariant:

    any two assignments of Y and processed U inputs having the same state
    induce identical residual functions on the still unprocessed U inputs.

Initially the state consists of Y, so the invariant is trivial. The state is independent of all unprocessed U bits. We can define arbitrary Boolean functions of the state using signed AIGs (for example a truth-table DNF); unreachable states can be assigned arbitrary values. This costs gates but introduces no direct occurrences of unprocessed U inputs.

Singleton i: for every reachable state sigma, let r_sigma be its well-defined residual function. Define the guard H_i(sigma)=1 iff r_sigma depends on i, i.e. iff there is some assignment of the other remaining U variables at which its i derivative is one. The current reader is

    w_i = x_i AND H_i(sigma).

The guard is nonconstant as a function of the original inputs: f is essential in i, so at least one state has guard 1; the successful peeling step supplies a full derivative-zero cylinder free in the other remaining U variables, so the state of that cylinder has guard 0. Append w_i to the state. When H_i=1, w_i retains the i bit. When H_i=0, the residual is independent of i, so losing that bit does not change the remaining residual function. Thus the invariant holds after the singleton.

Pair i,j: the Pair test provides a phase p in {0,1}^2 such that the three other pair cofactors are identical as functions of all outside inputs. Append the single signed AND of x_i,x_j whose value is 1 exactly at p. This retains precisely the exceptional/nonexceptional bit and hence suffices to preserve the residual function. Neither i nor j is read elsewhere.

At the end the invariant says f is a function of the final state. Synthesize an arbitrary decoder of that state. Every selected input has one direct reader and no direct occurrence in any guard or decoder besides that reader.

### Normalization does not reintroduce a selected primary

Fix any selected singleton i. There is an assignment to the other original primaries for which its guard is zero. The two assignments differing only in i then give identical values to every circuit gate: gates before its reader are independent of i, the reader is blocked, and there is no later direct occurrence. Therefore no gate can compute either phase of x_i as a function of the original inputs. For a selected pair, choose the blocking phase of the partner and use the same argument. Consequently a gate's semantic constant/primary/earlier-signal normalization can substitute a constant, an earlier gate literal or an unselected primary, but cannot substitute a selected primary in place of an internal gate. None of these substitutions increases its read count. Prune the dead cone. Essentiality of f in every selected input implies its unique read cannot disappear. This yields a normalized circuit with the required occurrences.

This proves exact feasibility without any optimization premise. The earlier maximum u_peel thus equals the largest possible number of singly read inputs among normalized realizations of f of unrestricted size. It is still only an upper bound on the largest number achievable among size-minimum realizations. Guard and decoder DNF construction can be exponentially expensive. Do not treat feasible peeling sets as small-budget synthesis witnesses.

## 3. Stronger obstruction: every circuit has a two-read normal form

The original motivation was to extend one-reader guard constraints to force a superconstant number of primary occurrences. There is an unconditional obstacle that survives semantic normalization and avoids identity-buffer tricks.

**Theorem.** Let n>=2 and let a Boolean function f have a signed AIG of s gates. Then f has a signed AIG with at most 6s+2n+3 gates in which each primary is read at most twice. If f has full support, the resulting circuit may additionally be normalized without increasing either its size or the read cap.

Proof: choose any two distinct anchor inputs a,b. First form the three nontrivial minterm signals with only two raw reads of each anchor:

    d = a AND b,
    p = a AND NOT d,     // a AND NOT b
    q = b AND NOT d.     // NOT a AND b

Set g=p OR q=a XOR b (one signed AND for OR). The two domains g=0 and g=1 partition the cube. The use of d as a guard is important: computing all three minterms independently would have three direct occurrences of each anchor. Here each anchor occurs exactly twice, in d and in its own second reader.

Encode the inputs by their masked positive rails in the two domains:

    g=1:  a -> p, b -> q
    g=0:  a -> d, b -> d
    for every other x: x -> g AND x, (NOT g) AND x.

There are 4 anchor gates and 2(n-2) other rail gates, total 2n. Every primary has at most two direct occurrences. The rail for signal v in domain j is semantically D_j AND v, where D_1=g and D_0=NOT g. Zero has rail 0, one has rail D_j. Within a domain, complemented literals are handled by

    rail_j(NOT v) = D_j AND NOT rail_j(v).

If an original gate computes v=u AND w, use the AND of the two appropriate signed operand rails. These identities hold pointwise on the full original cube; outside the selected domain all rail signals are zero. Repeat for every original gate in each domain, in topological order. One gate plus at most two operand-complement gates per original gate per domain gives <=6s gates. Apply the same rail complement operation to a signed output if needed (<=2 gates). OR its two domain rails (one signed AND) to obtain f. No further primary operand occurrences are introduced. This gives the stated 6s+2n+3 bound.

### Why this is not a redundant unary-buffer trick

Each domain contains both values of every primary coordinate. For the anchors this follows from the two pairs 00,11 and 01,10; for other coordinates they are free. Hence any function whose support is contained in just one of the domains cannot equal any signed primary (its complementary domain contains inputs at which that signed primary is one). All AND outputs in the construction except the final output OR's underlying complemented AND are domain-supported: d is supported in g=0, p,q in g=1, the underlying AND for g is NOT g, and every simulated gate or rail complement is domain-supported. The final AND computes NOT f; for full-support n>=2 it is not primary-equivalent or constant. Thus there are no primary-equivalent internal outputs anywhere in the construction. Replacing constants or duplicate signed internal functions by earlier internal literals, then pruning, never introduces a primary operand. The fully normalized version therefore has the same read cap. This uses semantic normalization only to establish existence, not an efficient general equivalence checker.

We could instead keep the explicit circuit and use ordinary local simplification for a uniform compiler; the size and syntactic read bound already hold without semantic normalization. The exact truth-table checker below carries out full semantic normalization for small circuits and verifies the stronger claim.

### Consequences and limitations

Define C_2(f) as the smallest signed AIG with at most two direct primary reads each. For every full-support f with n>=2,

    C(f) <= C_2(f) <= 6 C(f) + 2n + 3 <= 8 C(f) + 5,

using C(f)>=n-1. The same bound holds if C_2 additionally requires semantic normalization. More generally the first inequality and additive size overhead hold for arbitrary f without full support. Thus for any exponent alpha>1, a family has O(n^alpha) circuits iff it has O(n^alpha) two-primary-read circuits. This applies to the paired SAT decision function at the relevant lengths and to the guarded slice model after the existing basis transfer (the direct read statement is in the signed AIG model). It does not mean that a minimum-size circuit always has at most two primary reads. The transformation can increase its size by a constant factor.

This is an important barrier to the proposed reader program: one cannot prove a superlinear lower bound simply by showing that every normalized realization must use superconstantly many direct primary occurrences. There are normalized realizations with <=2n total primary occurrences, even for extremely hard functions. The obstruction is stronger than replacing each input by an equivalent identity buffer, because primary-equivalent internal gates are absent. It also rules out arguments that assume every circuit of size O(n^1.01) must have an average primary read count growing with n: if such circuits existed, this compiler would give equally small (asymptotically) circuits with at most two reads each. A minimum-circuit-specific tradeoff combining reads with internal sharing remains possible, but must account for the cost of the downstream simulation rather than only primary reads.

An alternative productive use: it suffices to exclude O(n^1.01)-size signed AIGs in this explicit bounded-primary-read model. The restriction on primary degree is now without asymptotic loss. However internal fan-out is still unrestricted; do not conflate this with read-twice formulas, bounded-read branching programs or bounded-wire-degree circuits. The two rails can be reused arbitrarily many times, which is exactly the resource the original lower-bound problem needs to charge.

## 4. Experimental replay

Run in this directory:

    node guard_read_normal_form_check.js

Seed 870018. The checker first enumerates all 65,536 four-input truth tables, keeps the 64,594 with full support, and examines all 16 candidate single-reader sets for each. For all 701,314 accepted sets (out of 1,033,504 subset tests), it constructs the sequential state and verifies the residual invariant after every processing step. It explicitly synthesizes 5,721 signed AIGs on a deterministic subsample of accepted sets, using truth-table DNFs for guards and decoder, normalizes by exact truth tables, independently re-evaluates the rewired gates, and checks the required primary occurrence counts in the live cone. 91,536 output truth-table entries, 8,861 selected primary read checks. Maximum retained gate count among these constructed examples: 39. This is not a minimum or an optimized size result.

For the two-read normal form, 3,000 random AIG attempts on n=2..4 inputs give 305 full-support outputs. Mask and simulate each circuit, verify the explicit raw gate bound, semantically normalize, and compare the resulting truth table with the original. 1,824 output truth-table entries and 733 primary read-cap checks, all passing; maximum normalized masked size 24. The final version uses d followed by the two guarded anchors (two reads for every primary), not the earlier three-read trial. The replay output is recorded exactly. Small random circuits are not a benchmark of asymptotic overhead or a proof of the theorem; the explicit algebraic compiler supplies the general proof. All assertions passed.

The previous guard-dependency replay already supplies the finite comparison to the ordinary exact single-restriction baseline (520 strict improvements); this round does not claim improvements against the stronger native recursive regional baseline or actual synthesis speedups. No new Lean proof. No literature-priority claim; bounded fanout reductions and signal masking are standard ideas, and the specific normalized primary-read statement is proved directly here.

## 5. Research direction

The original proposal to force many direct primary reads should now be refined. It is valid to obtain small linear improvements, as the earlier peeling result showed, but the asymptotic resource cannot be primary occurrences alone. The two-read normal form suggests studying the interface consisting of the first gates receiving primary information and the subsequent internal fanout/merge network. Because all raw inputs can be supplied through two readers, the main complexity must be in the downstream DAG. A useful next target is a gate-elimination or communication-style inequality on *internal* cut ports: constrain how many distinct context-dependent operand pairs can be assembled from a fixed set of previously computed signals, charge their actual routing and recombination gates, and test against the explicit masked two-read compiler and previous programmable router. Merely counting distinct gate signatures or cut residuals is still invalid by the earlier controls.

Native agent: independently audit both converse and compiler; replay the checker; retain the previous guard-cylinder lower bound as a finite size filter, not an asymptotic read-multiplicity route. If useful formalize the compiler with the existing signed AIG evaluation and restriction library. The explicit rail identities, primary occurrence count and no-primary-equivalent normalization argument are separable proof tasks. The stronger native baseline comparison remains outstanding. No production solver changes. L-clb-036 remains open.
