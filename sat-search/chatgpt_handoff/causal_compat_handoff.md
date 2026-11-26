# Causal response cuts: audit, compatibility colouring, and a Bob-entropy capacity

Date: 2026-11-26. Base [e67385e](https://github.com/Krapples/circuit-synthesis-research/commit/e67385efdb039b579611901d2f30e8ed2c88d38c). Native-agent round. Read [causal_response_handoff.md](causal_response_handoff.md) first.

**L-clb-036 remains open.** This round contains:

- an independent audit of the causal response-cut theorem, the vertex-split flow and the inverse-capacity gate charge. No error was found;
- a sound, strictly finer cut capacity, built from compatibility colouring and Bob's input entropy, which also works in the flow and additive-charge argument;
- a new independent checker with negative controls;
- a ceiling statement showing that the restriction families built so far cannot give n^1.01 through any sound charge.

There is no superlinear bound, no Lean proof, no production change and no claim of priority.

## 0. Setting and notation

Fix a signed AIG C, a partition of its vertices into A and B with the output in B, and data primaries S in A. All other A primaries are fixed to public constants. Bob's varying primaries Y lie in B, over an allowed domain. The remaining notation follows the earlier handoff:

- F and R are the forward and reverse port vertices.
- D(v) is the set of A-local data ancestors of v.
- R(v) is the set of A-local reverse ancestors of v.
- T_v(x) is the local response table with the reverse ports R(v) treated as formal inputs.
- c(v) = min(|D(v)|, 2^|R(v)|).

New notation:

- D*(v) is the set of data ancestors of v along *any* directed path.
- ρ_v(x,y) is the vector of actual values of R(v) at the input (x,y).
- G_v(x) is the function y -> v(x,y) on Bob's domain.
- μ(v) is the minimum size of a set W of *data-free* vertices (vertices with no S ancestor) that meets every directed path from a varying Bob primary to v. If v itself is data-free, μ(v) is not used.

## 1. Audit of the committed theorem (Phase 1)

Each step was checked separately. Verdict: **sound as stated.**

1. **Response-table count.** With B-to-A edges broken, the value of v is a function of the A primaries in its A-cone and of the formal values on R(v). Every B vertex feeding v's A-cone is in R(v) by the union recursion. The non-data A primaries are fixed, so T_v depends on x only through D(v). Hence #T_v <= 2^min(|D(v)|, 2^|R(v)|).

2. **Reconstruction with data-dependent feedback.** The decoder runs in global topological order and so evaluates each reverse port before any K vertex that reads it. Its value at an actual reverse vertex may depend on x through earlier forward ports. That does not matter: the table is evaluated at the actual history, and T_v(x) agrees with the true value of v at every formal history, the actual one included.

   An A-recursion from a forward port that never meets K cannot reach a free data bit. If it did, it would trace an A-only path from S to F that avoids K. The quantifier is "K meets every A-only S-to-F path", which also covers length-zero paths where a data primary is itself a port. That is exactly what the proof uses. The forward port values are correct by induction, so the B part and the output are reconstructed correctly.

3. **Output ownership.** The theorem requires the output to be in B. Otherwise the output is an A vertex that the cut need not meet. The handoff states this premise.

4. **Metadata placement (one-active-group lookup).** The joint residual is a function of Bob's whole domain, which here consists of the legal metadata and low-query values. The A constants are shared by all contexts. The theorem allows Bob's domain to be any subset. Varying the A constants between contexts would give different A-cuts and no single code, as the handoff warns. Verdict: correct.

5. **Flow.** The cut on vertex-split edges gives min cut = min Σ_{v∈K} c(v) over A-only vertex cuts. This is at least log2 N, so by max-flow/min-cut the maximum flow is at least ceil(log2 N), and the capacities are integral.

   Under injectivity, each data primary has capacity min(1, 2^0) = 1 and the flow is exactly |S|, so each source sends one unit. The path decomposition in the acyclic A-graph gives Σ_i d_i <= Σ_P w(P) = Σ_v load(v)/c(v) <= s_A.

   No gate is counted twice:
   - Each original A gate contributes at most 1 in total.
   - Primaries contribute 0.
   - The forward-port endpoint is counted, matching `dist` in the checker, which charges the reader when stepping to it.

   **Remark:** the argument does not need integrality. A fractional flow of value |S| with real capacities gives the same inequality, since every path carrying source i's unit weighs at least d_i. Section 3 uses this.

6. **"Sum of the m smallest d_i" for non-injective N.** A flow of value m >= ceil(log2 N) with unit source capacities uses at least m distinct sources, each sending at most 1 unit. Sound.

7. **Strict topologies.** The local variant has port capacity 2k and the all-feedback variant has internal capacity k, with demand M = 2^k. Both were re-derived and recomputed independently (Section 4, item 3).

**Replay.** Both committed checkers reproduce their committed replay files byte for byte, apart from CRLF line endings:

- `node causal_response_check.js`, seed 870022: 213 random AIGs, 4,428 cuts, 777 flows, maximum charge 21.
- `node causal_lookup_check.js`, seed 870023: 72 cases, 336 residual rows.

**Checker caveat (minor, does not affect soundness).** The committed checker's `cap` takes D relative to the subset S0 but R globally, which matches the paper definition. Its flow test of the additive charge reuses the same `dist` recursion as the paper, so it is not an independent check of the path metric. The new checker re-implements the recursion separately.

## 2. Compatibility colouring and the Bob-entropy capacity (Phase 2)

**Conflict graph.** At an A vertex v, data assignments x and x' *conflict* if there is an allowed y with

    ρ_v(x,y) = ρ_v(x',y)   and   v(x,y) ≠ v(x',y).

The conflict uses the *same* y and the *actual* histories of both assignments. Nothing assumes that a history realizable for x is realizable for x'. Let χ_v be the chromatic number of this graph, or any upper bound from a proper colouring.

**Theorem 1 (compatibility cut).** For every A-only cut K, log2 N <= Σ_{v∈K} log2 χ_v.

*Proof.* Fix proper colourings col_v and encode x by (col_v(x))_{v∈K}. To evaluate f(x,y), the decoder simulates C in topological order with dummy data. At v ∈ K it already knows y and the actual history h = ρ_v(x,y), by induction. It picks any x* with col_v(x*) = col_v(x) and ρ_v(x*,y) = h; x itself qualifies. It outputs v(x*,y). Because x and x* share a colour, they do not conflict, so v(x*,y) = v(x,y). The rest of the induction is as in the committed proof. Equal colour vectors therefore give equal residuals. ∎

**Lemma 2 (hierarchy).**

    χ_v <= min(#T_v, #G_v),   #G_v <= 2^min(|D*(v)|, 2^μ(v)).

Hence the *structural* capacity

    c⁺(v) = min(|D(v)|, 2^|R(v)|, 2^μ(v))

satisfies log2 χ_v <= c⁺(v) <= c(v).

*Proof.*
- If T_v(x) = T_v(x'), the same history gives the same value, so x and x' do not conflict.
- If G_v(x) = G_v(x'), the same y gives the same value, so they do not conflict.
- Equal codes therefore never conflict, and colouring by T or by G is proper.
- Let W be a data-free separator of size μ(v). Every vertex in v's cone that W does not separate from Bob is a function of x, the constants, and the values on W. W itself is a function of y alone. So for fixed x, G_v(x) factors through {0,1}^|W|. This gives #G_v <= 2^(2^μ). The bound #G_v <= 2^|D*(v)| is immediate.
- Finally, |D(v)| <= |D*(v)|. ∎

So c⁺ is non-circular: it needs only the graph, the partition and S. The semantic quantities χ_v, #T_v and #G_v are used here only for checking and diagnosis.

**What c⁺ detects that c misses.** For fixed data, the feedback history at v varies only with Bob's input. It carries at most μ(v) bits of Bob entropy, however many reverse wires there are and however much data they carry. The old capacity counts 2^|R(v)|, so an adversary can inflate it with *Bob-free echo*: reverse wires that are functions of forward data, possibly gated by one Bob bit.

Example (checked, Section 4, item 2). A forwards group parities z_j. B returns e_j = z_j AND b, where b is the AND of all query bits. Each data bit is XORed with an echo before the group XOR. With k groups of g bits:

| | c (old) | c⁺ |
|---|---|---|
| Port capacity | k g + k | 3k |
| Min cut | k g = \|S\|, passes | 3k, rejects |

The k = 4..7 instances need |S| = 16, 35, 66, 133 and get min cuts 12, 15, 18, 21. Also, the committed all-feedback topology, which c rejects only through an internal cut, is rejected by c⁺ **at the ports** (2k vs M). Its query parity g is a single data-free vertex, so μ = 1.

**Chronology and the cost of feedback.** μ is nondecreasing along data-carrying paths: a separator for a descendant must cut before the first data-carrying vertex. So feedback gains capacity only by bringing in new Bob entropy through data-free vertices. Each extra unit of μ needs another vertex-disjoint data-free path from a fresh Bob primary into the cone (by Menger). Data-dependent feedback is free in the adversary's gate budget but counts for nothing in c⁺.

**What c⁺ still misses (limitation, checked).** Structural capacities can be inflated by *tautological* Bob dependence. For example, t_j = NOT(q_j AND NOT q_j) is constant 1, data-free and in B. ANDing it into the leaves of the compress-then-query topology raises R and μ, so both c and c⁺ pass the INDEX demand of 8. The semantic colouring capacity gives min cut 3 and rejects (Section 4, item 8). Normalized circuits forbid constant gates and duplicate functions, which excludes this particular padding. Whether normalization-proof Bob padding exists is open. c⁺ is therefore a sound upper bound but not robust to semantically useless structure. The exact semantic χ is robust but circular.

**Correlations (joint realizability).** Encoding by the *joint* colour vector gives log2 N <= log2 #{joint vectors} <= Σ log2 χ_v. In 265 of the 859 tested cuts the joint count was strictly below the product. No structural bound for the joint count beyond min(|∪D(v)|, Σ c⁺(v)) is claimed, and no flow version of it is known: a set capacity of that form need not be submodular, which polymatroidal flow requires.

## 3. Replacing c in the flow and the additive charge (Phase 4)

**Theorem 3 (refined additive charge).** Let κ be any per-vertex capacity such that log2 N <= Σ_{v∈K} κ(v) for every A-only cut K. Examples are c⁺, or log2 of any proper colouring count. Assume the residual map is injective on S. Let d_i^κ be the minimum over A-only paths from i to F through vertices with κ > 0 of Σ_gates 1/κ(v). Then

    s_A >= Σ_{i∈S} d_i^κ.

*Proof.* The min vertex cut is at least |S|, and cutting all sources costs exactly |S| because κ(data primary) <= 1. Under injectivity it is also at least 1, since a data bit's two values give different residuals. So the real-capacity max-flow has value |S|, and each source sends one unit, possibly split over several paths. Decompose the flow fractionally into paths. Every path from i weighs at least d_i^κ. So Σ_i d_i^κ <= Σ_P f_P w(P) = Σ_v load(v)/κ(v) <= #{A gates with load > 0}. ∎

Each original A gate is charged at most once and primaries are not charged. With κ = c⁺ every weight is at least the old one, so the charge never decreases.

**Corollary (Bob-entropy path condition).** Suppose every A-only data-to-port path contains at least L gates v with min(|R(v)|, μ(v)) <= h. Then under injectivity s_A >= |S| L / 2^h. This holds regardless of how much data-dependent feedback reaches those gates. The committed corollary needed |R(v)| <= h.

**Explicit missing premise for L-clb-036.** Call it (PF_ε): for every circuit C computing SAT_n, some legal restriction and partition give an injective residual on S with Σ_i d_i^{c⁺} >= n^(1+ε). Together with Theorem 3, (PF_ε) implies size >= n^(1+ε). It is *stronger* than the target: the charge never exceeds s_A, so (PF_ε) is a sufficient strategy, not an equivalent restatement. It is not proved.

**Ceiling statement (proved, elementary).** Every sound charge computed on a restriction f_ρ is a lower bound on the size of every circuit for f_ρ. It therefore never exceeds C(f_ρ). The restrictions built so far have upper bounds:

| Restriction | Upper bound |
|---|---|
| Batched lookup | O(n) |
| Enabled lookup, fixed π | O(n) |
| Enabled permutable lookup | O(n log² n) |
| Tseitin and parity couplings | O(n) |
| Andreev-type projections, including the packed permutable one | O(n polylog n) circuits |

The cubic witness promises are quasi-linear only in the regimes constructed so far, via the cubic cover bound O((n + 3^h + 2^(h+t)) polylog n). The ceiling applies to those regimes.

For these the charge is at most O(n polylog n) = o(n^1.01), whatever the capacity refinement. A proof of n^1.01 through this route therefore needs a SAT restriction with no quasi-linear circuit, which is itself a superlinear lower bound for an explicit function. The inequality s_A >= Σ d_i is also tight on natural circuits: on INDEX mux trees placed in A the charge equals s_A exactly (3, 9, 21 for k = 1..3).

**Does SAT force superlinear growth?** Nothing found here suggests that legal SAT restrictions force it. The tested lookup, permutation-network and enabled-lookup controls all have charge Θ(s_A) = Θ(n).

## 4. Checker and controls (Phase 3)

[causal_compat_check.js](causal_compat_check.js), seed 870031, [replay](causal_compat_replay.txt). This is an independent implementation with its own AIG builder, max-flow, μ computation and decoder.

On each small instance it computes, per A vertex:
- c, c⁺ and μ, by vertex max-flow;
- the exact #T_v and #G_v;
- the conflict graph and a greedy proper colouring.

It asserts the full hierarchy:
- log2 #T <= c;
- log2 #G <= min(|D*|, 2^μ);
- min(log2 #T, log2 #G) <= c⁺ <= c;
- the colouring is proper and no T-equal or G-equal pair conflicts.

On each cut it asserts log2 N <= Σ log2 χ <= Σ c⁺ <= Σ c. It runs the **colour decoder**, which knows only the colours at K, y and its own simulated values, and checks that it reproduces every output bit and that equal colour vectors imply equal residuals. It runs three real-capacity max-flows (c, c⁺, colouring) and checks that each cut certificate equals its flow and that each flow is at least log2 N. Under injectivity it checks charge(c) <= charge(c⁺) <= charge(χ) <= s_A.

Totals:
- 170 analysed instances (160 random signed AIGs), 1,036 vertices, 859 cuts, 142,760 decoder evaluations, 32 injective instances.
- Falsification sweep: 1,500 further random AIGs with 6–25 gates and heavy interleaving of A and B, all A primaries as data, testing log2 N <= mincut(c⁺) <= mincut(c) against exact residual counts. log2 N equalled the c⁺ min cut in 150 of them.
- No assertion failed.

Strictness counts (upper capacities, not size improvements):
- c⁺ < c at 1 random vertex. c⁺ needs |D| >= 3 and |R| > μ, which small random circuits rarely produce.
- χ < min(#T, #G) at 7 vertices; χ < 2^c⁺ at 107 vertices; #G < #T at 32 and #T < #G at 40.
- The χ min cut was below the c⁺ min cut on 6 instances; the c⁺ min cut was never below the c min cut in random circuits.
- On the 32 injective random instances the refined charges never exceeded the old ones; the maximum charge was 21 in all three.

The refinements bite on adversarial interfaces (echo, tautology), not on natural small circuits.

Controls (D = semantic, S = structural):

| Control | Data | Min cut c / c⁺ / χ | Demand or charge | Verdict |
|---|---|---|---|---|
| 1. Random signed AIGs (D) | ≤ 6 | as above | as above | sound |
| 2. Echo k=4,5,6,7 (S) | 16/35/66/133 | 16/12, 35/15, 66/18, 133/21 | \|S\| | c passes, **c⁺ rejects** |
| 2'. Echo k=2,3 (D) | 4/6 | 4/4, 6/6 | log N = 1 | sound (g = 2, no gap) |
| 3. Local feedback k=4..7 (S) | 2^k | k/k | 2^k | both reject (ports 2k/2k) |
| 3'. All feedback k=4..7 (S) | 2^k | k/k | 2^k | both reject; **ports M vs 2k** |
| 4. INDEX mux tree in A, k=1..3 (D) | 2^k | 2^k all | charge = s_A = 3/9/21 | tight, no gain |
| 4'. Mux with levels ≥ 1 in B (D) | 2^k | 2^k all | charge 3/6/12 | no gain |
| 4''. Mux tree k=4..7 (S) | 2^k | 2^k/2^k | 2^k | passes (correct circuit) |
| 5. Programmable 4-wire switch network (D) | 4 | 4/4/4 | charge 11 of 37 gates | no gain |
| 6. Enabled lookup r=2, fixed π (D) | 4 | 4/4/4 | charge 6 | no gain |
| 7. Mux with tautology leaf padding (D) | 4 | 4/4/4 | charge 17 | padding raises charge (\|D\| = 1 gates) |
| 8. Tautology-inflated local feedback (D) | 8 | 8/8/**3** | 8 | **structural fooled, semantic rejects** |

Not replayed as circuits:
- The normalized two-primary-read compiler. It changes the circuit by a constant factor, so it cannot raise any sound charge above O(s). It is relevant only through normalization (Section 2).
- The packed SAT layouts. The committed lookup checker covers their residual injectivity.
- The Andreev–Tseitin and cubic witness controls. They are covered by the ceiling statement: they are promise families with quasi-linear upper bounds (for cubic, in the regimes built), and per [witness_compatibility_synthesis.md](witness_compatibility_synthesis.md) they are negative controls for proxy combinations.

## 5. Summary of status

| Claim | Status |
|---|---|
| Committed response-cut theorem, flow and charge | Independently audited, sound; replays reproduce |
| Theorem 1 (compatibility colouring cut) | Proved here; checked by an explicit colour decoder |
| Lemma 2 and c⁺ = min(\|D\|, 2^\|R\|, 2^μ) | Proved here; strictly stronger on echo topologies (checked k = 4..7) |
| Theorem 3 (refined additive charge, fractional flow) | Proved here; checked on 32 injective instances |
| Ceiling: charges on f_ρ are at most C(f_ρ) | Elementary; all current restriction families are quasi-linear |
| (PF_ε) for SAT | Open; sufficient, not necessary |
| Normalization-proof Bob padding | Open |
| Submodular joint capacity for a polymatroidal flow | Open |

Next targets:
1. Find a restriction of SAT with no known quasi-linear circuit for which the residual structure still forces long low-μ paths.
2. Alternatively, prove that normalized circuits admit a structural μ that is robust to useless Bob dependence.

Do not treat c⁺ rejections as size bounds for arbitrary SAT circuits. Do not add charges over overlapping partitions.
