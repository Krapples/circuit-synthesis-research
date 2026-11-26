# Packed batched lookup: asymmetric directed port capacities

Date: 2026-11-26. Base [f0c899b](https://github.com/Krapples/circuit-synthesis-research/commit/f0c899b30300299d70b22c27cdf15cca4b84b572). Read [packed_welllinked_handoff.md](packed_welllinked_handoff.md) first. This round strengthens the graph-cut method in a different direction: asymmetric information flow and distinct outgoing signal ports, with a packed batched lookup projection having single-copy table and query bits. It proves a tight (up to constants) directional communication tradeoff, and a one-way frontier storage bound. These are paper results and finite regression, not an unrestricted superlinear gate bound or Lean verification. L-clb-036 remains open. No production solver changes or novelty-priority claim.

## 1. Model and port accounting

Use the original paired SAT decision circuit, arbitrary binary gates, free complemented wires, arbitrary fanout. Partition original vertices into A and B. Define a to be the number of DISTINCT vertices in A with at least one wire to B, and b analogously for B to A. Call these directed ports. These counts are never greater than the corresponding directed operand-wire counts, and can be much smaller with high fanout.

For any fixed constant restriction whose remaining A primaries are Alice's input and B primaries Bob's, the original circuit gives a deterministic communication protocol with a bits from Alice to Bob, b from Bob to Alice. Process vertices in public topological order; whenever a port vertex is evaluated, its owner sends its bit once, and the recipient retains it for every subsequent reader. A primary can be sent at its topological evaluation step. Gate computations are local given the received earlier values. Known constants can be sent as scheduled dummy bits or omitted; the fixed schedule of a+b messages is a valid upper bound. The output is evaluated by its owner, not necessarily announced. As in the previous handoff, the inputs compatible with a transcript form a rectangle; the accepting subset is also a rectangle because the output owner depends only on its own input and transcript.

This immediately improves the previous fixed matching edge cut inequality to: number of aligned matching demands crossing the cut <=a+b (distinct port vertices). Likewise the previous constant-factor arbitrary edge-cut lower bound is valid for a+b, not just crossing wire count. This argument does not require fan-in two; the number of distinct transmitted signals is what matters. A directed cut with zero reverse ports is a one-way protocol; for a prefix of any topological evaluation order the forward ports are the live values with remaining readers.

## 2. Batched lookup and the asymmetric rectangle theorem

For integers r>=1, M>=2, define

    F(H,q) = AND_(j=1..r) H_j[q_j],

where Alice holds r independent arbitrary M-bit tables H_j and Bob holds r addresses q_j in [M]. Consider any deterministic fixed-schedule protocol with a data-to-query bits and b query-to-data bits, output known to either party.

**Theorem.**

    a+b >= r log_2 M,
    a+b+r >= r M / (2 * 2^(b/r)).

If Bob (query side) owns the output, additionally

    a * 2^b >= log_2(1 + (2^M-1)^r).

The last bound implies a*2^b>=r log_2(2^M-1); for r=1 the exact RHS is M. These are bounds on directional budgets, not a charge summed over many overlapping cuts.

Proof of the first bound: the matrix of one INDEX factor has full column rank M over R, since its rows include all one-hot table vectors. The batched matrix is the Kronecker product of r copies, hence rank M^r. The accepting transcript rectangles sum to the matrix, so rank<=2^(a+b).

Proof of the second bound (a direct richness argument). Restrict Alice to tables having at least M/2 ones in every group. There are at least 2^(r(M-1)) such rows by complement symmetry, and each has at least (M/2)^r positive query columns. For a fixed row, there are at most 2^b distinct transcripts as Bob varies his input: Alice's messages are determined by her row and the previous Bob bits. Each such rich row therefore belongs to an accepting rectangle containing at least (M/2)^r / 2^b query columns. Assign each rich row to one such transcript. Since there are at most 2^(a+b) transcripts, some accepting rectangle has row set X of size >=2^(r(M-1)-a-b) and query set Y of size >=(M/2)^r / 2^b. The row set may also include other rows; use the complete accepting rectangle.

Write Y_j for the coordinate projection of Y to its j-th address. Every H in X must have H_j[t]=1 for every t in Y_j, since every pair in X times Y accepts. Hence

    log_2 |X| <= r M - sum_j |Y_j|.

Since |Y|<=product_j |Y_j|, arithmetic-geometric mean gives

    sum_j |Y_j| >= r |Y|^(1/r) >= r M / (2 * 2^(b/r)).

Combine the two bounds on |X| and rearrange. This proof uses no randomized communication, no round count bound and no independence assumption about the selected accepting rectangle. The protocol may have arbitrarily many alternating rounds.

Proof of the additional strategy bound when Bob owns output: encode Alice's deterministic strategy by listing the a outgoing bits she would send along every one of the 2^b full strings of Bob bits, ignoring whether that Bob string is consistent with any actual Bob input. A deterministic circuit simulation can evaluate Alice's local region using supplied earlier Bob bits even for unrealizable transcripts. More generally define arbitrary responses off the protocol tree. The encoding has length a 2^b. Two data rows with the same strategy have identical behavior for every Bob query and hence the same residual Boolean function on the queries. There are exactly 1+(2^M-1)^r distinct residuals: if some table is all zero the function is zero, and otherwise its nonempty accepting Cartesian product uniquely determines every table by taking projections. Counting encodings proves the bound. It is important that the output is on Bob's side: if Alice owns output, she may distinguish rows in her local output even when her messages agree. The rank and richness bounds do not require that convention.

These are standard types of asymmetric communication arguments (richness and strategy counting), specialized here and proved directly. Background: Miltersen, Nisan, Safra and Wigderson, On Data Structures and Asymmetric Communication Complexity, STOC 1995 / JCSS 1998, https://doi.org/10.1145/225058.225093 and https://www.brics.dk/RS/94/41/index.html. No claim that the communication lemma itself is novel.

## 3. Tight total-cost tradeoff and unequal domains

With a budget b of reverse bits (rather than necessarily exactly b used), the optimal total deterministic communication for the above problem with Bob output is

    Theta(r log_2 M + r M 2^(-b/r)),   M a power of two.

For b<=r log_2 M, set t=floor(b/r). Bob sends the t high bits of each query; Alice sends the 2^(k-t) bits of the selected block of each table; Bob uses the remaining query bits and ANDs the answers. The protocol uses rt<=b reverse bits and r M 2^(-t)<=2rM2^(-b/r) forward bits. For b>=rk Bob sends all query bits and Alice returns one combined answer bit. The lower bound follows from Section 2: if X=rM2^(-b/r)>=4r, then a+b>=X/4; otherwise rk>=r>=X/4. Along with rank this gives the matching constant-factor lower bound. Here b is an available budget, so a protocol using fewer reverse bits still obeys the displayed lower bound with b substituted. The formula does not mean the minimum FORWARD bits alone are tight for all b (the richness estimate charges total cost).

Unequal domain variant: let group j have d_j>=1 table bits and d_j possible query choices. Exactly the same proof gives

    a+b >= sum_j log_2 d_j,
    a+b+r >= (r/2) (product_j d_j)^(1/r) 2^(-b/r),
    a * 2^b >= log_2(1+product_j(2^d_j-1))   [Bob output].

The rich row count is >=2^(sum d_j-r) and each has >=product(d_j/2) positive queries. No common power-of-two domain assumption is needed in the lower bound. This variant is useful for partially split packed layouts.

## 4. Exact batched packed SAT grammar

Use the repository's existing Andreev table packing idea, but omit the selector parity rows and make each of r groups an independent lookup. Let k>=1, M=2^k, ell the largest power of two <=max(1,floor(k/2)), P=2^ell, B=M/ell, lo=log_2 ell. Assume r<=M^c for fixed c when discussing asymptotic word length.

Each group has k address variables a_0,...,a_(k-1) whose values are pinned by k unit clause polarities. These k sign bits are the free query coordinates, each appearing exactly ONCE in the physical word. It has a rooted binary guard tree on the high k-lo address bits, using 2B-1 guard variables. The root is pinned true. For each child z representing g AND l (l is the appropriately signed next address literal), use the three clauses (-z OR g), (-z OR l), (z OR -g OR -l). Processing high bits most-significant first gives leaf index floor(q/ell), exactly one true guard.

For every group j and pattern p in [P], reserve a variable V_(j,p). For each t in [ell], append a clause whose low-address literals are false exactly when the low query equals t, and whose final literal pins V_(j,p) to bit t of p. Thus the selected low address determines every dictionary variable uniquely. For each block i of the M-bit table, let p be its ell-bit data pattern, and append

    (-guard_i OR V_(j,p)).

The one true guard makes the corresponding table bit required to be one. Other guard clauses are inactive. Each group is satisfiable iff H_j[q_j]=1. All namespaces are disjoint across groups, so the whole formula is satisfiable iff their conjunction F is one.

Exact common-width IDs: there are A=r(k+2B-1) non-dictionary auxiliaries. Let Q be the least power of two >= A+rP. Reserve zero-based IDs Q+jP+p for dictionaries, j=0..r-1, and Q+rP,...,Q+rP+A-1 for auxiliaries. All have width w=log_2 Q+1. Since Q and every group dictionary base are multiples of P, the low ell digits of its V ID equal the table pattern exactly. All tag/group and higher identifier digits are constant. Each data block clause therefore contains ell single-copy free data bits, whose exact physical positions are invariant over every table and query assignment. Query polarities are also single-copy fixed coordinates, disjoint from all data bits. In the grammar a literal of width w takes 2w+4 bits; the low digit j of the positive V literal in a two-literal data clause starts at clause offset (2w+4)+3+2j, zero-based. The explicit checker verifies these positions by mutations.

The word has O(r(k+B+P ell (lo+1))) literal occurrences. For k large, B=Theta(M/k), P<=sqrt(M), ell=Theta(k), and P ell (lo+1)=o(M/k). The width w=O(log(rM)) and is Omega(k). With r<=M^c, n_(k,r)=Theta(rM), and the free data bits number rM=Theta(n). The query bits number rk. All lengths are even and independent of data/query. For a fixed gamma>=0 choose r=2^floor(gamma*k), so n_(k,r)=Theta(2^((1+gamma)k)) and the scale ratio is eventually bounded. Extend to all sufficiently large even n by the same largest-k choice and 10/14-bit fixed tautology padding as in the prior handoff. This round checks the actual unpadded grammar, not the padding; the previous padding proof is reused. No copies, complements or nonlocal encodings of a free coordinate appear.

This is an explicit new packed restriction of SAT; the address/data packing is inherited from the earlier Andreev construction. It is not the unit-only layout from the separator theorem, and its terminal set need not coincide with that earlier terminal set. Do not implicitly identify their physical positions when combining different restrictions at the same length.

## 5. Directed SAT cut theorem, partial layouts and topological frontiers

For every circuit deciding paired SAT at the packed length, fix any partition with all designated table bits on the data side A and all query bits on B. All other physical primary inputs are fixed constants of the grammar. Then the port counts a,b must obey Section 2, because the circuit simulates the deterministic protocol of Section 1. The output owner is unchanged by the restriction. This is a condition on the original directed graph, not on a compiled circuit for the restriction.

In fact partially split groups can be used. For group j, suppose d'_j of the M data coordinates lie in A and q'_j of its k address coordinates lie in B. The q'_j free query bits partition the M addresses into 2^(k-q'_j) subcubes obtained by fixing the other query bits. Some such subcube contains >=ceil(d'_j / 2^(k-q'_j)) of the A data positions. Fix the other query bits to that slice, and select those d_j positions, fixing all other table bits to constants. Restrict Bob's query domain to the d_j corresponding addresses. This is a restriction of the communication domain, not a claim that the query subset is itself a coordinate subcube. The actual SAT circuit must be correct on all these inputs. For any selected set of groups with d_j>=1, set all other groups to constant-one lookups. Apply the unequal-domain theorem. The argument also works in the other orientation, as a separate restriction using the opposite role for the graph sides. These bounds are simultaneous necessary conditions on the same graph, but cannot be added as disjoint charges without a proof of port disjointness.

For a topological prefix A, no edge goes from B back to A. If a group has useful data in A and remaining query bits in B, the output belongs to B whenever its residual function depends on a B query bit. The forward port count then obeys the strategy lower bound at b=0:

    a >= log_2(1+product_j(2^d_j-1)).

In the full split this is >=r(M-1), so a linear number of distinct intermediate or primary values must remain live in a schedule that processes all table bits before all query bits. This is a storage/frontier bound for that order, not an all-orders lower bound. If every selected domain has size one the output-owner condition must be checked separately. If a group has d_j>=2, its lookup is essential in at least one B query coordinate, ensuring the output is on B for a topological prefix. For arbitrary order, some cuts may have little usable data/query separation; no theorem forces every schedule to process the table before the queries.

### Quantitative interpretation

For r=M=2^k the packed length is Theta(M^2). If b<=rk/2, the richness inequality gives a+b>=Omega(r sqrt(M))=Omega(n^(3/4)). The ordinary rank bound is only rk=Theta(sqrt(n) log n). If b=O(r), the richness bound gives a+b=Omega(n). More generally if a+b<=r L for L>=0, rearrange to obtain

    b >= r log_2(M/(2(L+1))),

with a trivial negative RHS when L is too large. Thus a small total interface requires almost all k query bits per group to travel toward the data side, unless a large forward interface pays for the missing query information. The one-way exact strategy estimate is stronger when b=0 and the output is on B.

These are sharper directional constraints than rank alone for the same function: its undirected real log rank is only rk, while a one-way data-to-query protocol requires nearly rM bits. They do NOT imply a superlinear size lower bound for unrestricted SAT. The port count at each cut is <=n+s, the bounds do not exceed O(n) in the full packed family, and cut ports may be reused across many restrictions. A lower bound beyond linear needs a disjointness or resource tradeoff on multiple internal cuts, not mere summation.

## 6. Negative control and relation to prior architecture results

The batched packed lookup promise has a fixed O(rM)=O(n) signed AIG: each group is a balanced mux tree on its M table inputs, with k query bits shared across levels, and AND the r outputs. Each mux uses three signed AND gates and each group uses M-1 muxes. This is an actual simple explicit topology for the fixed promise, not an unrestricted SAT upper bound. The full direction tradeoff is thus already necessary for a linear-size function. In particular a circuit can obey it by routing query bits across many local readers or evaluating the lookup on the table side. It does not falsify the earlier graph-only expander routing obstruction or provide a cut-to-prescribed-flow implication.

The distinct port accounting from Section 1 applies also to the previous unit-only packed matching and well-linkedness restrictions. The two packed families can be combined as separate necessary conditions for any full SAT circuit, but there is no proof of an additive charge between them or of a topology-preserving guarded Hamming-slice compiler. No directed analogue of the all-terminal arbitrary-cut theorem with the same unit-only terminal set is asserted here.

## 7. Executed regression

Run: node packed_directional_check.js. Seed 870021. Actual packed grammar: 112 cases k=1..7, r=1,2,4,8, 39 SAT/73 UNSAT; independent token parser and unit propagation agree on all cases. Unit propagation resolves all remaining clauses on the positive cases; negative cases conflict. The mathematical gadget semantics proves the unpinned result. 224 exact single-bit coordinate mutation checks for both data and query bits; largest word 238,944 bits, largest table total 1,024 bits. Finite small k has large fixed overhead; not an empirical asymptotic density claim.

Communication: 32 complete small protocols with output on either side and different splits of query bits, 43,680 data/query assignment entries, 16,600 transcript/accepting rectangle checks, 32 richness inequality checks, 16 strategy checks with Bob output. These explicit protocols use the block-retrieval construction; the Alice-output variant sends remaining query bits back after the block transmission. They do not enumerate all protocols or optimize their costs.

Additional explicit signed mux AIGs: 90 partitions of actual batched lookup circuits, 113,040 truth-table evaluations, 50,658 transcript rectangle checks, 8 forward-only partitions with query-side output, maximum 21 AND gates. The final replay checks both crossing operand-wire and distinct-source port transcripts on all 90 cuts: 50,658 additional port transcript rectangle checks, directional richness/rank and exact strategy inequalities. Deduplication reduces transmitted bits on 58 cuts, by up to 11 bits in a single cut. All assertions passed. [Actual stdout](packed_directional_replay.txt). No new padding/slice check, full SAT AIG synthesis, general graph optimization or Lean verification. A preliminary unused unaligned-ID draft was removed before running and committing the aligned implementation.

## 8. Next milestone

The previous matching cut conditions encode symmetric exchange capacity; the new asymmetric profile distinguishes data access from query routing. A concrete next experiment is to extract directed ports for actual native AIGs and compare memory/frontier costs across legal restrictions with fixed stable IDs. Investigate whether metadata can program many independent lookup groups with different orientations while maintaining invariant physical roles, then derive a sound charge for their simultaneous downstream coordination. Beware: both the fixed batched mux and earlier programmable sorting controls obey all necessary inequalities with small circuits. The normal form with at most two primary reads also survives; its internal ports can carry information cheaply. Do not assume overlapping cuts are independent or that a small number of reverse wires implies small total communication unless the theorem's directed split premises hold. A superlinear distinct-gate invariant is still needed. Native agent: audit richness, strategy counting, partial-domain restriction, grammar alignment and actual port protocol; replay and optionally formalize in separable pieces. No production integration or claim of novelty over existing asymmetric communication techniques. L-clb-036 remains open.
