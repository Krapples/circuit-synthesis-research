# Cofactor reader bounds and single-NOT replacement (2026-11-26)

Follow-up to [two_fork_handoff.md](two_fork_handoff.md). Two additional sound paper pruning lemmas for the nine-gate core. Neither has been Lean-checked or integrated into the proof-producing CNF runner. No upstream closure; L-clb-036 remains the primary long-term target.

## 1. Exact zero/one-fork cofactor classifier

For a monotone truth table g after dropping inessential variables, let m be the number of essential variables. Count binary AND/OR gates, allowing unrestricted free negations and constants. For m<=1 the binary cost is zero. For m>=2, the minimum is at least m-1 by live edge counting. Equality holds iff g is monotone read-once, by the zero-excess argument and exact read-once formula DP. If not read-once, cost at least m.

At cost m, the live graph has exactly one fork with two outgoing occurrences (NOTs allowed without charge). Its upstream formula has a set U of distinct primary variables, and every path from those primaries to the output passes through this fork. If U is all variables, the downstream circuit computes a one-bit function of the fork, hence g is read-once up to complement, contradiction. Otherwise U is a proper nonempty subset. There must be exactly two residual tables on the complement W as the U assignment varies. By monotonicity, these are the rows at all-zero and all-one U, respectively A<=B. Define h(U) to be the indicator of row B. It is monotone, full support on U, and equals the fork function up to complement, so h is monotone read-once. The outer quotient G(z,W) has G(0,W)=A and G(1,W)=B. It is monotone and all W are essential. It is a formula on the W variables once and z twice, with arbitrary signs on z; after pushing NOTs to leaves, each W leaf must be positive by monotonicity. Both h and G can be tested by the exact formula-position DP used in the two-fork checker. Conversely, if these tests pass for some U, connect a read-once h to the two z leaf positions in the outer formula, with free complements. Its binary count is (|U|-1)+|W|+1=m. Thus the test is an exact classifier of cost m after excluding read-once cost m-1. If none passes, cost >=m+1, not necessarily equality. The proof handles inessential original variables by fixing them to constants and simplifying.

[cofactor_reader_check.js](cofactor_reader_check.js) evaluates all 728 restrictions fixing a nonempty subset of the six physical variables (3^6-1). 59 distinct raw projected tables (arity included), 15 restriction instances strengthened over support-only bounds. The DP uses sets of BigInt truth tables, exact, no solver. Formula sets: positive read-once at arity 5 has 472 tables, at arity 4 has 52; repeated variable 0 with arbitrary signs on its two occurrences gives 2,864 tables at arity 5 and 245 at arity 4. All checks passed; see [replay](cofactor_reader_replay.json).

## 2. Union of direct reader gate IDs

Let U be any nonempty subset of the original primaries. Let r(U) count DISTINCT binary gates having a direct operand in U. Fix the primaries in U to any assignment rho. Every one of those r(U) gates becomes a constant or signed alias after local simplification (one fixed operand of AND/OR suffices), regardless of other simplifications. A topological substitution removes them simultaneously, without introducing any new binary gate. Therefore

    r(U) <= b - C_bin(f|rho).

Taking the maximum of certified cofactor lower bounds over all rho gives a necessary reader-count cap for every candidate with b=8. This is a union of original gate IDs, not operand occurrence count and not the sum of per-primary reader counts. It is valid with one internal NOT or free negations.

For individual inputs in zero-based order 0..5, the max cofactor bounds are [6,5,5,6,6,6], so reader caps are [2,3,3,2,2,2]. For five pairs (0,3),(0,4),(3,4),(3,5),(4,5), a cofactor has lower bound 5, hence at most three distinct binary gates directly read either member. All 63 set caps and witnessing restriction phases are in the replay (phase is compressed into the listed input order, not a physical bit mask). These are necessary constraints only. Adding CNF cardinality clauses requires faithful OR-of-selector indicator for each gate, and a sound proof of the cofactor lower bounds if the clauses are part of an upstream formal certificate. Do not add them to the proof search by assumption.

## 3. One-NOT monotone replacement lemma

For an eight-binary candidate with exactly one internal NOT, let h(x) be its operand (a monotone signal), and replace its output by an independent bit z. The rest of the circuit now computes a monotone function G(x,z). The target f(x)=G(x,NOT h(x)) is monotone. Therefore G(x,0)<=f(x)<=G(x,1).

Let P be the minimal positive masks of f, Z its maximal negative masks. If a monotone replacement signal u(x) satisfies

    u(p)=1 for every p in P with h(p)=0,
    u(t)=0 for every t in Z with h(t)=1,

then G(x,u(x))=f(x). Proof: for a minimal positive p, if h(p)=0 use u(p)=1 and the original equality, otherwise G(p,0)=1 so either u value works. For a maximal negative t, if h(t)=1 use u(t)=0, otherwise G(t,1)=0. The substituted output is monotone in x, so agreement on the positive/negative boundary implies agreement everywhere.

In particular if h>=f pointwise, choose u=0. If h<=f pointwise, choose u=1. Both substitutions turn the NOT output into a constant and eliminate at least one binary gate that reads the NOT (the NOT is live and is not output), contradicting the eight-binary minimum. Thus h must be incomparable with f. Equivalently some minimal positive p must have h(p)=0 and some maximal negative t must have h(t)=1. In a truth-table CNF, for each possible NOT operand h, enforce those two existential boundary clauses conditional on selecting h as the unique NOT operand. These are cheap necessary constraints; the current runner does not include them.

More generally if u is an earlier available monotone signal and is another operand of a direct binary reader of the NOT, the safe replacement eliminates that reader by idempotence. This rules out such a gate arrangement. Require u to precede the NOT (or be a proved NOT-independent available operand with acyclic substitution); using a signal depending on the NOT would be circular. This criterion is sufficient for replacement, not necessary. A stronger semantic version tests u(p)=1 only when G(p,0)=0 and u(t)=0 only when G(t,1)=1.

For this table P=[19,21,22,24,34,36,40], Z=[15,18,20,49]. Among all 30 raw distinct-input AND/OR pair operands, h comparable with f occurs in exactly five cases: x1 AND x5, x2 AND x5, x3 AND x4, x3 AND x5 (h<=f), and x4 OR x5 (h>=f). All indices zero-based. Direct exact 64-row boundary checks were performed in the chat runtime. These exclude the NOT reading such a gate, wherever it occurs, but do not exclude those gates appearing elsewhere.

## 4. Native handoff

Use the original 22-shard certificate runner first if cheap enough. If certificate size/runtime is problematic, consider the optional reader and boundary pruning lemmas above, after independently checking soundness. The CNF proof alone still does not certify the exact Lean statement. Verify current upstream row and no duplicate PR; upstream uses a one-file and 512 KiB limit. A compact structural proof or accepted reduction may be preferable to embedding enormous DRAT traces. No Lean toolchain in this runtime; no PR submitted. No new asymptotic claim.
