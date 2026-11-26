# Stable gate-role ledgers: ingress capacity and programmable-role obstruction

Date: 2026-11-26. Base ChatGPT handoff [2f69df4](https://github.com/Krapples/circuit-synthesis-research/commit/2f69df44f735042859531da6d20bc353151cfb79). Read [witness_compatibility_synthesis.md](witness_compatibility_synthesis.md) first. Current native RESEARCH_NOTES.md blob 40ab7e6fb8bbe2bec9761af622bdba74310b87b8 and [cubic cluster/hub audit](../results/cubic_cluster_hub/README.md) inspected. L-clb-036 remains open. This round gives a valid multi-context gate-role inequality and proves that its natural topology relaxation cannot improve the ordinary single-restriction bound for singleton blocks. A second negative control falsifies bounds on the number or linear rank of distinct restricted functions at a stable mixed gate. No superlinear gate-count lower bound or new Lean theorem. No production solver changes.

## 1. Native updates

The native agent independently audited the cubic cluster series, common hub kernel and batched Walsh table identity. Explicit signed AIG scores matched direct scores on 5,660 assignments; the Walsh implementation was larger at every tested positive marginal dimension. The native seven-output cubic control has full linear marginal dimension, no image-preserving proper coordinate restriction, and a linear-size fixed-metadata AIG. It has a Tal-dependent formula lower bound Omega(n^(20/7)/(log^2 n log log n)). The native two-output construction distinguishes zero-coordinate kernels from arbitrary fixed-phase coordinate kernels; local support identity, converse and period lemma are Lean checked. These controls supplement, not replace, the Andreev-Tseitin combined control from the preceding handoff. Do not duplicate the completed audits. The new work below is independent of their exact cubic details.

## 2. A sound ingress ledger

Use the signed AIG model with fan-in-two ANDs, free complemented edges and constants. Take a live output cone, discard trivial constant gates if necessary, and partition its primary inputs into disjoint nonempty blocks X_1,...,X_r. Use syntactic support (ancestors), not semantic support of a possibly cancelling gate. Assume the output has ancestors from at least two blocks. A pure gate or primary has ancestors in exactly one block; a mixed gate has ancestors in at least two blocks. Nonconstant literals inherit the support of their underlying wire. Constant wires can be eliminated before classification.

For stable original gate IDs, classify every gate once:

- a_i: number of pure gates of block i.
- b_i: mixed gates having exactly one pure operand, of block i (the other operand is mixed). Call these attachments.
- c_ij: mixed gates having two pure operands from distinct blocks i,j. Call these seeds.
- d: mixed gates having two mixed operands. Call these merges.

These cases partition all live gates. Let b=sum_i b_i, c=sum_(i<j)c_ij and a=sum_i a_i. Total s=a+b+c+d. There is at least one seed if the output is mixed. Within the induced mixed-gate graph all mixed gates reach the mixed output, because syntactic support is nondecreasing along directed paths. Each mixed gate other than the output has at least one operand occurrence into a mixed reader, so b+2d >= (b+c+d)-1, giving d>=c-1. Occurrences, not only distinct edges, are counted. No bound on fan-out is assumed.

For a nonempty subset S of block indices, let L_S be ANY sound lower bound on the largest minimum AIG size of a cofactor obtained by assigning all blocks outside S to constants. It can be the exact largest minimum or a certified weaker lower bound. The same fixed original circuit must realize every cofactor. Define

    cap(S) = d + sum_(i in S)(a_i+b_i) + sum_(i<j, i,j in S)c_ij.

**Ledger inequality: L_S <= cap(S) simultaneously for all S.**

Proof: fix any outside assignment. Every gate in a pure fixed block becomes constant. Every mixed gate with at least one pure operand from a fixed block becomes a constant or an alias/complemented alias; the AND of a constant and a literal needs no gate. Propagate constants and aliases in topological order. Retain only the resulting live cone, optionally structurally hash duplicates. No new AND gate is needed for a deleted gate. Each surviving AND can be associated with its distinct original ID, and none of the excluded classifications can survive. Thus at most cap(S) original gates remain, independently of the values of the fixed outside bits. Taking the maximum cofactor demand proves the inequality.

This is a genuine capacity bound for first ingress roles: a pure or attachment gate can survive only when its block is free, a seed only when both of its blocks are free. Merges receive capacity for every context, because neither original operand is pure. In particular for singleton retained blocks,

    sum_i L_{ {i} } <= a+b+r d.

This is NOT a capacity bound for every gate with the same constant independent of r.

There is a second sound, complementary cut constraint. Let p_i be the number of DISTINCT underlying pure wires from block i that occur as operands of mixed gates. A complemented wire is the same bit, not a second independent port. Let N_i be the number of distinct residual functions of all outside inputs obtained by varying block i over all assignments. The entire outside behavior of the circuit is determined by the p_i pure wire values: substitute formal variables for those boundary wires, and every remaining mixed gate can be evaluated in topological order using them and the other blocks. Hence N_i<=2^p_i. Counting occurrences of block-i pure operands gives

    ceil(log_2 N_i) <= p_i <= b_i + sum_(j != i)c_min(i,j),max(i,j).

Also p_i<=|X_i|+a_i, though raw syntactic inputs not reaching the mixed boundary need not all occur as ports. These constraints handle arbitrary correlations among pure signals. They are ordinary cut information inequalities applied to a stable topology, not an entropy sum over different circuit copies.

Together these equations and inequalities define a small integer relaxation in the ingress counts for a specified partition. One may add ordinary gate-elimination/cofactor bounds independently. It is sound to minimize s subject to necessary inequalities, but not to interpret a feasible profile as a realizable circuit. Fixed topologies can additionally be rejected by their known counts. The next section identifies a limitation even if every L_S is exact.

## 3. Exact limitation of the count-only relaxation on singleton blocks

Let f have full support on n>=2 primaries and take singleton blocks X_i={x_i}. Work with a normalized AIG, in which any syntactically singleton-supported gate can be replaced by a constant or signed literal (there are only four unary functions). Recompute syntactic support after substitutions. Thus for the purposes of a size lower bound we may set a_i=0. Every full-support block has N_i=2 and needs at least one ingress occurrence.

For arbitrary cofactor lower demands L_S>=0 on every nonempty proper subset S of [n], put

    B = max( n-1, max_(nonempty proper S) (L_S+n-|S|) ).

This is the standard single-restriction baseline for full-support functions in this model: fixing n-|S| essential inputs to constants can eliminate at least that many gates when the chosen restriction is nonconstant. One way to prove it is to use a minimum live circuit and process the fixed inputs one at a time, deleting a first reader for each still-essential input; if an input has already disappeared, the usual excess/restriction counting argument supplies the total count. For the precise checked version use the repository's existing excess_restriction theorem, with its essential-input and nonconstant-restriction premises. For L_S=0 the independent source-count bound n-1 already dominates L_S+n-|S|. For positive L_S a cofactor attaining the demand is nonconstant. Nothing in the following relaxation obstruction needs the baseline to be tight for f.

**Claim: the ingress count relaxation cannot certify a lower bound larger than B, for ANY choices of the cofactor demands satisfying these definitions.**

Construct a feasible abstract profile of total B:

    c_12=1, all other c_ij=0,
    b_i=1 for i>=3, b_1=b_2=0,
    d=B-(n-1), all a_i=0.

All ingress requirements are met exactly once, c=1, and d>=0=c-1. For any nonempty S the number of potentially surviving ingress gates is

    |S minus {1,2}| + 1[{1,2} subset S] >= |S|-1.

Hence cap(S)>=B-(n-1)+|S|-1 = B-n+|S| >= L_S. The profile satisfies every ledger demand simultaneously, even with exact cofactor minima, and costs B. Adding the standard single-restriction bounds to the relaxation therefore makes its optimum exactly B. This proof is only about the stated abstraction; it is not a limitation theorem for all multi-context methods, all partitions, or richer topology constraints involving actual operand identities, signs, and propagation. The profile need not realize f (or even a minimum irredundant topology). In fact the surplus merges in this abstract profile may have no way to carry the required distinct semantic roles. This is precisely the missing information.

The result explains why the first attempt to turn the gate-role ledger into a new numerical lower bound failed. It is useful to know this in advance of expensive larger LPs or SAT encodings. For singleton partitions, merely increasing the number of cofactor contexts or providing stronger exact L_S values will not help this count-only relaxation. The next refinement must keep something discarded here: actual correlations of gate operands or the way aliases propagate into shared descendants. The existing native restriction counters already capture some such facts for concrete topologies; we should use those rather than claim novelty for simple constant propagation.

## 4. Programmable mixed gates defeat function-diversity and role-rank capacity

For an even number N of source bits, construct one fixed programmable permutation network. A compare-exchange sorting network, with each comparator replaced by a conditional swap controlled by a query bit, suffices. The comparator control bits are the swap decisions for sorting the keys of the desired permutation. With key bits supplied instead, implement their comparisons as well. A bitonic network with padding to a power of two has O(N log^2 N) switches, and fixed-size Boolean conditional swaps have constant signed AIG cost. For simplicity restrict N to powers of two for the asymptotic statement. Every permutation has a query setting; the circuit topology and original gate IDs are fixed throughout.

At the output of the network, form N/2 bank gates

    g_j(x,q)=r_(2j)(x,q) AND r_(2j+1)(x,q),

where r_i are routed source bits. XOR all bank outputs to obtain one Boolean output. Every bank gate is internal and live for N>=4. For a fixed query context pi the bank gives disjoint pair products, and the output is the matching quadratic form. As pi ranges over permutations, EACH stable bank gate realizes every pair monomial x_a x_b with a!=b. These binom(N,2) Boolean functions are linearly independent over GF(2), by uniqueness of multilinear representation (or evaluate at the weight-two assignment of each pair). So the linear dimension of the span of restricted functions of a SINGLE live internal gate is binom(N,2). Each of N/2 gates has this property simultaneously; at each context all these gates have pairwise disjoint operand pairs.

This disproves universal per-gate constant or polylogarithmic capacity bounds based merely on the number or GF(2) rank of distinct gate functions, even if one requires roles to use disjoint variables within a context or excludes the final output gate. In fact one may sum the role ranks over this bank and get Theta(N^3), while the circuit is O(N log^2 N). Counting query input bits as part of the input length does not rescue a superlinear inference based solely on this role measure: total length with explicit controls is O(N log^2 N). This is an explicit small-circuit negative control, not an assumption about a minimal representation of the function. A lower-bound invariant valid for every circuit cannot assign small capacity to these stable IDs on the basis of their restricted truth functions alone.

A SAT-specific paper embedding is also available. Use N equal-width variable IDs, one per physical source slot, with a unit polarity encoding x_i and identifier metadata permuting those slots into N logical variables. Append fixed AND gadgets for adjacent logical pairs, and an XOR chain with a pinned output (either parity). The resulting paired words have length Theta(N log N); under the promise that the tags form a permutation, the source polarities occupy fixed physical coordinates and the SAT predicate is the matching quadratic form or its complement. Sort (tag, source polarity) records by their tags and use the same fixed bank followed by XOR. Comparators now cost O(log N) per record, and the entire promise circuit is O(N log^3 N)=O(word_length log^2 word_length). The usual padding and Hamming balancing can be applied. No actual grammar replay of this new pairing embedding is claimed here; the physical AIG below checks the abstract explicit-control network. The paired embedding is not needed for the general obstruction.

## 5. Experiments, with exact scope

Run in this directory:

    node gate_role_ledger_check.js
    node programmable_gate_roles.js

The ledger checker enumerates all 65,536 four-input truth tables and filters the 64,594 with full support. For one-, two- and three-input cofactors it enumerates sets of available signed truth functions, adding a nontrivial new AND function at each step. Complement classes are canonicalized. Constants and identities never need a gate in a minimum free-phase circuit; functions already available need not be added twice. Search is exhaustive through cap 1,3,4 respectively; any function not reached gets the valid lower bound cap+1, not an exact minimum. In particular no unsupported claim about exact parity_3 cost is needed by the replay. The 710 distinct cofactor-demand vectors are compared against 32,631 ingress profiles (at most eight seed/attachment slots, with merge count optimized analytically). The explicit profile from Section 3 fits this finite cap; the theorem proves the no-improvement statement independent of it. In this sample every relaxed optimum equals the standard baseline; there are no improvements. This does not prove exact four-input circuit minima.

The same checker generates 500 random signed AIGs with 3..6 primaries and arbitrary block partitions of size 2..4, extracts the live original IDs, and checks 22,912 restrictions. Constant propagation, alias elimination and hashing keep original representatives. It checks that every survivor has only pure operands from retained blocks, the survivor count respects cap(S), and the simplified function equals the original cofactor on every remaining input. It also checks 1,453 boundary residual cardinality constraints (for pure output cones the mixed-boundary implication is not asserted). Seed 870016. All assertions passed. [Actual output](gate_role_ledger_replay.txt).

The programmable gate checker constructs an actual signed AIG for six sources, using a fixed 15-comparator insertion sorting schedule with explicit query switch controls, three bank ANDs and their XOR. There are 99 live AND gates. Exhaustively evaluating all 720 permutations and all 64 source assignments gives 46,080 output checks and 138,240 bank-role checks. Each of the three stable internal ANDs has exact GF(2) truth-table rank 15 across contexts, computed by binary elimination on BigInt truth vectors. All assertions passed. [Actual output](programmable_gate_roles_replay.txt). The finite insertion schedule is quadratic; the asymptotic paper bound uses the standard bitonic network, not an extrapolation of measured gate counts. An earlier combined checker attempt failed an assertion; splitting and correcting the replay produced these independently passing scripts. No failed data is being used as proof. The scripts are finite regressions, not Lean verification.

## 6. A more focused next step

The two barriers point to a specific missing invariant.

- The pure-ingress count is too coarse: it lets every merge survive every context and knows nothing about which pair of intermediate signals enters it.
- The number/rank of actual functions seen at a mixed gate is too permissive: routing lets one gate change roles almost arbitrarily. Requiring many simultaneous disjoint pairs does not fix it.

Therefore a future gate-role ledger should measure **the cost of realizing the operand-routing changes**, not the resulting role labels. A natural small experiment is to record, for each stable original edge, the equivalence relation of contexts under which its source literal has the same restricted truth function, and for each stable gate the paired operand signatures and resulting aliases. Combine these with the native forced-derivative and restriction-cone rules. Test whether a proposed capacity inequality remains valid under programmable swaps (the routing gates themselves are charged) and under the packed Andreev-Tseitin and native cubic controls.

One precise finite target: compare circuits that realize the same set of output cofactors but differ in how their original operand signatures co-vary across contexts. Seek a sound implication of the form "if these local signature partitions and original topology occur, this many additional distinct reader/merge gates are required." This is a topology-sensitive hypothesis, not a numerical lower bound or pruning rule. Use counterexample search on small AIGs and exact native synthesis; do not simply assume independent gate roles are expensive. The goal is a conditional inequality strictly beyond constant/alias elimination on a concrete topology, then a universal optimization over topology. The present ingress abstraction alone cannot supply it.

Native-agent tasks: replay both scripts, audit the simple count/cut proofs and the explicit profile limitation; reuse the already verified excess_restriction and current native restriction counters. Do not integrate a singleton ingress-profile filter as a claimed stronger lower bound. If useful, add a separate stable-ID operand-signature ledger to the experimental workflow, not the production solver until a proof and differential checks exist. Preserve the asymptotic target L-clb-036 as open. No novelty claim for standard graph counts, entropy cut facts, sorting networks, or the underlying gate elimination method.
