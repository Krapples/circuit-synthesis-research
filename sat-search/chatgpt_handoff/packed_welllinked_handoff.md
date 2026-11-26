# Arbitrary terminal cuts, prescribed matching demands, and the routing-gap obstruction

Date: 2026-11-26. Base [3340781](https://github.com/Krapples/circuit-synthesis-research/commit/3340781f4d41f4d27bad347a94a39627fbe5f3cd). Read [packed_separator_handoff.md](packed_separator_handoff.md) first. This round strengthens the previous balanced separator theorem to all terminal cuts, derives exact cut requirements for each fixed programmed slot matching, gives geometric wirelength tradeoffs, and proves a bounded-degree linear-graph negative control for the inference from cut requirements to low-congestion matching routes. All general theorems below are paper proofs, not Lean verification. L-clb-036 remains open. No production solver changes or literature-priority claim.

## 1. Model and retained coordinates

Use precisely the preceding packed unit-clause construction: m=2^k slots, ell=floor(k/4), P=2^ell, Q a sufficiently large power of two, ID Q+tag*P+pattern. There are P dictionary unit clauses at tag zero, and m programmable unit slots. Local mode checks h(x_i)=s_i, opposite signs on a common unique nonzero tag impose x_i!=x_j, and unique unused tags are inactive. All IDs have the same canonical width w=log_2 Q+1. Pattern position j in slot i has physical word offset (P+i)(2w+6)+3+2j (zero-based). The T=m ell designated terminals are single-copy original primaries. Word length Theta(k 2^k), padding to all sufficiently large even lengths as before, so T=Theta(n). The dictionary signs can be fixed after seeing a proposed partition; physical terminal positions do not change.

The undirected circuit graph has vertices for gates and physical primaries, edges for operand wires. Gates have fan-in <=2 and arbitrary Boolean functions, arbitrary fan-out. Free constants are public. Parallel wires can be counted with multiplicity, or treated as one undirected edge since a single transmitted source bit suffices. A separator partition A,B,C has no A--B edge. For a set of vertices A, delta(A) denotes all undirected edges crossing A vs its complement.

## 2. Arbitrary cuts: average rank rather than a universal dictionary

For disjoint terminal parts A,B,C, let a_i,b_i,c_i count the ell pattern coordinates of each slot assigned to these sets. Put a=sum a_i, b=sum b_i, z=sum c_i, u=min(a,b), M=sum min(a_i,b_i). We prove that whenever u>0 and z<=u/64, a constant restriction leaving free only some pattern bits in A and B has communication matrix of real log-rank at least u/128.

First consider local tests. Draw a symmetric zero-diagonal ell-by-ell matrix R uniformly by choosing independent upper-triangle entries. For any two disjoint coordinate sets I,J, the rectangular cross block R[I,J] has independent uniform binary entries. Let d=min(|I|,|J|). Its expected GF(2) rank is at least d/2: transpose if necessary, expose d rows in order, and each row increases rank with probability >=1/2 because the span of previous rows has dimension strictly smaller than the number of columns. This includes d=0. By linearity of expectation, one common R has

    sum_i rank_2 R[I_i,J_i] >= M/2.

No independence between different slots' cross ranks is necessary. This replaces the earlier simultaneous union bound and works even when one side contributes a single bit.

Set h(x)=XOR_(i<j) R_ij x_i x_j. For a slot with cross rank r, its signed character matrix after fixing all other coordinates to zero has real rank 2^r, as in the preceding handoff. If F is the indicator of h=1, rank(J_all-ones-2F)<=1+rank(F) implies rank(F)>=2^r-1. For r>=2, log_2 rank(F)>=r/2. For r=1, some cross entry is one. Restrict to that pair of bits, fixing every other bit to zero; the restricted quadratic has a nonzero mixed term, so its four values have odd XOR. One of its two acceptance-phase indicators has three ones and a nonzero 2-by-2 determinant. Thus for r=1 also, some acceptance phase has log-rank >=r/2. For r=0 the slot may be inactive, contributing rank one. Choose signs independently and multiply the disjoint local communication factors (Kronecker product). The log-rank is at least M/4.

If M>=u/32, this proves the desired u/128 bound. Otherwise use paired inequality tests:

- Discard slots with c_i>=ell/8; their total number of pattern bits is at most 8z<=u/8.
- Discard remaining slots with both a_i,b_i>=ell/8; their total number of pattern bits is at most 8M<u/4.
- Each remaining slot is dominated by A or B with >3ell/4 bits in its dominant side. All A bits in B-dominant slots together are at most M<u/32 (and symmetrically).

Consequently each side has >u/2 pattern bits in its own dominant slots, and hence at least u/(2ell) such slots. Pair that many distinct A-dominant and B-dominant slots. The two dominant coordinate sets within each pair overlap in >ell/2 positions. Leave only those common positions free, fix every other pattern bit zero, program opposite signs on a unique shared tag, and make all unpaired slots inactive. Each pair's inequality matrix has full rank 2^r for r common positions, since it is J-I. The product log-rank is at least u/4, stronger than required. Integer counts need no asymptotic rounding loss: the number of available slots is an integer at least the real lower bound u/(2ell). This argument works for any ell>=1, and the asymptotic scale uses ell growing with k.

Thus the only hypothesis on cut terminals is z<=u/64, with no balancedness threshold. The choice of dictionary is a constant restriction, not a uniform algorithm for finding R. The preceding stronger simultaneous dictionary statement for large mixed cuts remains valid, but is unnecessary here.

## 3. Communication cost with no output-announcement bit

For an edge partition A vs B, process the original circuit in topological order and transmit the value of each crossing operand wire to its receiver's owner. At most |delta(A)| bits are communicated; duplicated wires may share a transmission. Local gates use locally known inputs and received bits. The output owner can evaluate the decision, and need not announce it to the other party.

For a vertex separator partition A,B,C, fix all C primaries publicly (plus other required metadata and unused terminals). Both parties evaluate each C gate by receiving its at-most-two operands from A/B as needed. Gates in A or B use local and earlier C values. At most 2|C| bits are communicated. The output is known to its owner or both if in C.

The usual deterministic transcript rectangle property gives a real rank upper bound of 2^cost even without an output-announcement bit: for each fixed transcript, compatible input assignments form a Cartesian product. If the output is known to Alice, accepting assignments within that rectangle are a subset of Alice's factor times Bob's factor, because Alice's output is determined by her local input and transcript. The same holds for Bob, or output known to both. Each accepting transcript therefore contributes a rank-one (or zero) matrix, and disjoint accepting rectangles sum exactly to the decision matrix. This removes the additive one-bit loss from the prior presentation, important for tiny cuts.

Combining with Section 2 proves, for the fixed terminal set T and EVERY vertex set A of the original circuit graph,

    |delta(A)| >= min(|T intersect A|, |T minus A|)/128.

For EVERY separator partition A,B,C,

    |C| >= min(|T intersect A|, |T intersect B|)/256.

Indeed if |C|>u/64 the latter is automatic; otherwise z<=|C|<=u/64 and Section 2 gives 2|C|>=u/128. Both statements include u=0 trivially. All restrictions are ordinary constants on original input coordinates. No copying, complemented duplication, or graph-changing compiler is used.

## 4. Node-disjoint linkage consequence

For any disjoint equal-sized subsets X,Y of the designated terminals, each of cardinality r, the graph contains at least ceil(r/257) mutually vertex-disjoint X--Y paths (endpoints distinct; pairing not prescribed).

Proof: any vertex set C meeting every X--Y path leaves X minus C and Y minus C in disjoint unions of components, which can be put on opposite sides of a separator partition. If |C|>=r the claim is immediate; otherwise each side contains at least r-|C| terminals. The preceding separator theorem implies 256|C|>=r-|C|, or 257|C|>=r. Apply the set-to-set vertex form of Menger's theorem with endpoint deletions allowed in the separator. The same proof works for unequal X,Y with r the smaller size. In the terminology of graph minors this is constant-factor terminal well-linkedness, not the exact node-well-linked property that requires r paths. See Chuzhoy's grid-minor literature for the conventional distinction, e.g. https://arxiv.org/abs/1305.6577 (terminology background, not a premise of our proof). No assertion that prescribed partners are joined by these paths.

## 5. Stronger fixed-matching cut inequalities

The preceding packed layout also yields a different, exact demand inequality. Fix ANY matching of whole slots before considering a circuit cut. Program opposite polarities and a unique common tag for each matched slot pair; unmatched slots are inactive. Fix dictionary and all metadata once, for example use h=0. The restricted function on its pattern inputs is the conjunction of word inequalities x_i!=x_j over the matching.

For every matched slot pair, demand one connection for every corresponding pattern-coordinate pair (same low digit position). These demands form a matching on physical terminals, with no endpoint repeated.

Now choose any edge cut A vs B. Let r_ij count aligned pairs crossing this cut within matched slots i,j. If r_ij>0, fix all noncrossing positions in the two patterns to zero, leaving precisely the crossed endpoints free. The two crossing orientations may both occur in one slot pair; simply label Alice's bits and Bob's bits by position. Inequality is still exactly inequality between their r_ij-bit strings. Its matrix is J-I with real rank 2^r_ij. If r_ij=0, fix the two patterns to distinct constants (possible since ell>=1); the factor becomes one, without changing tags or signs. The remaining factors multiply, giving log-rank exactly the total number of crossed demanded pairs.

For a vertex separator A,B,C, count only demanded pairs with one endpoint in A and one in B. Fix C endpoints and all other noncrossing bits just as above. The same rank argument works; the metadata remains fixed across cuts. Therefore, for EVERY matching of slots and EVERY cut, simultaneously,

    number of matching demands crossing an edge cut <= |delta(A)|,
    number of matching demands crossing A--B of a vertex separator <= 2|C|.

These are exact capacity cut conditions for the prescribed demand matching, not just a constant-factor bound on the smaller side. The graph of the original SAT circuit must satisfy all of them. The function for one matching is fixed before the choice of cut; only pattern constants vary. We do not infer that the circuit provides actual disjoint or low-congestion paths connecting those particular partners.

## 6. A graph-level obstruction: all cut conditions can coexist with large routing congestion

This is the precise gap between cut capacity and simultaneous routing. There exist bounded-degree simple graphs with O(T) vertices and edges, with the designated T terminals grouped into m slots of ell bits, satisfying ALL the exact matching edge and vertex cut inequalities above, and the constant-factor terminal cut inequalities, but with some whole-slot matching requiring Omega(log m) edge congestion to route its aligned demands. Even fractional path flows have this congestion lower bound.

Here is a self-contained existence proof. For T sufficiently large, take d=32 independent uniform permutations of T terminals and join each vertex to its image in each permutation, ignoring loops and repeated edges. The resulting simple graph H has maximum degree <=2d and O(T) edges. With positive probability every S of size k<=T/2 has at least k/2 external neighbors. Otherwise all images of S lie in S union D for some D of floor(k/2) outside vertices (pad if necessary). For a fixed S,D the probability is at most (1.5 k/T)^(dk), by sampling without replacement in each permutation. There are at most (eT/k)^k (2eT/k)^(k/2) choices of S,D (also valid when floor(k/2)=0). The union failure probability is bounded by

    sum_(k=1..floor(T/2)) [e sqrt(2e) 2^(3/2) (3/4)^d]^k < 1

at d=32, using k/T<=1/2. Choose a successful H. For each of its edges keep the original edge and add one separate length-two path with a fresh intermediate vertex. Call the resulting simple graph G. It has O(T) edges, maximum degree <=4d, and terminal vertices are precisely the original T vertices.

For any edge cut of G with terminal side S the original crossing H edges number at least min(|S|,T-|S|)/2 by expansion. Each supplies at least two distinct crossing edges in G (direct edge plus one edge along the new path), regardless of where intermediate vertices are placed. Thus |delta(A)|>=min(|S|,T-|S|), which dominates the crossing count of EVERY terminal matching, including the aligned slot demands. For a vertex separator A,B,C, take the smaller of the two original terminal sides S. Its H-neighbors outside S all lie in C, since direct H edges are retained. Therefore |C|>=|S|/2 and 2|C| dominates every matching demand crossing A--B. The generic constant-factor inequalities are consequently satisfied as well.

Now label the T terminal vertices arbitrarily as m slots of ell positions, with m even (as in the packed family). Choose a uniformly random perfect matching of slots. Each terminal's partner is uniform among the m-1 terminals at its position in other slots. For fixed maximum degree D=4d, a ball of radius L=floor((log_D m)/2)-1 has O(sqrt(m)) vertices. Thus a terminal's partner is at distance >L with probability 1-O(1/sqrt(m)). By expectation there exists a slot matching whose T/2 aligned terminal pairs have total shortest-path distance Omega(T log m). A fractional routing of unit demand for each pair along paths must have total edge load at least that distance sum, since every path is at least the shortest-path distance. But G has O(T) edges, so its maximum edge load is Omega(log m). This also applies to integral routing.

This is a graph-only counterexample: it does not construct a SAT-deciding circuit with this graph or show that every SAT circuit has high prescribed-pair congestion. It shows even the combined exact cut inequalities, for all slot matchings simultaneously, plus bounded degree, do not imply constant-congestion matching routing. Consequently one cannot sum distance costs for prescribed partners and charge each original gate/edge once based solely on these inequalities. A circuit-semantic lemma beyond cut information would be needed. Even an eventual Omega(n log n) gate bound would not alone settle the n^1.01 threshold.

## 7. Geometric wirelength and local-connection architecture bounds

A separate useful consequence of arbitrary-cut expansion does not require any prescribed routing. Assign each vertex an arbitrary real coordinate p(v). Let mu be a median of the terminal coordinates. By the elementary coarea identity,

    sum_(edges uv) |p(u)-p(v)|
      = integral_R |delta({v:p(v)<=t})| dt
      >= (1/128) integral_R min(#terminal coordinates<=t, #>t) dt
      = (1/128) sum_(terminals x) |p(x)-mu|.

The first equality counts each edge on exactly the interval between endpoints; the last equality counts distance to a median. Ties at endpoints have measure zero. Sum this inequality over each coordinate of an embedding into R^d to obtain

    total L1 edge length >= (1/128) sum_(terminals x) ||p(x)-mu||_1,

where mu is any coordinate-wise terminal median. More generally for a fixed slot matching, applying the exact matching cut inequality to every level cut gives total L1 edge length >= sum_(matched terminal pairs xy) ||p(x)-p(y)||_1. These are geometric endpoint-distance statements, not costs of routing along the circuit graph. They are valid for any placement, including crossing wires and unbounded fanout.

If terminals occupy distinct cells of Z^d, fixed d>=1, the number of cells within L-infinity radius R of mu is <=(2R+3)^d. Take R=c_d T^(1/d) sufficiently small; at least T/2 terminals have distance Omega(T^(1/d)) from mu. Thus total L1 wirelength is Omega_d(T^(1+1/d))=Omega_d(n^(1+1/d)). If each gate wire has endpoint L1 length <=L, the wirelength is at most 2s L by fan-in two. Hence

    s L = Omega_d(n^(1+1/d)).

This gives, for fixed-range lattice circuits, quadratic size in one dimension, n^(3/2) in two dimensions, and n^(4/3) in three. With s=O(n^1.01), some wire has endpoint length Omega_d(n^(1/d-0.01)) when d<100. These are restricted physical-layout models; terminals must have distinct cell positions (or fixed bounded occupancy, with a constant change); wires need not be planar. The bounds do not prohibit long wires in general circuits and are not claims about VLSI time, area, energy, or fabrication constraints. The standard relation between bisection and wirelength has a long literature, e.g. Leighton, New Lower Bound Techniques for VLSI (1982), https://dspace.mit.edu/entities/publication/b0fb2340-0ac2-4f3d-9fe6-454e8a091156 and Karchmer-style communication layout approaches; our direct coarea proof does not need a VLSI model theorem. No novelty claim.

As before, these arguments concern the original paired SAT graph, not a topology-preserving transfer to the guarded Hamming slice. The fixed-width unit-clause promise still has quasi-linear unrestricted sorting circuits. The graph example and sorting control are complementary: the first falsifies a specific cut-to-routing inference, the second establishes an actual small-circuit negative control for treating broad connectivity as hardness.

## 8. Executed finite replay

Run: node packed_welllinked_check.js from this directory. Seed 870020. The final committed checker enumerates all 64 symmetric zero-diagonal four-bit dictionaries and all 50 nonempty disjoint cuts at that width: 50 exact expectation checks and 3,200 rank comparisons using GF(2) for cross blocks and F_101 for communication matrices. The modular nonzero minor is also a real-rank lower certificate; the character identity is valid modulo 101 since powers of two are invertible. Inequality matrices of size <=16 have nonzero constant eigenvalue modulo 101.

320 partition contexts on 32 four-bit slots, including 142 unbalanced cases (smaller side <T/8), minimum smaller side one terminal. 64 cases have too many C terminals and invoke only the trivial large-separator case, 180 local and 76 dominant cases. In the latter two, the checker exhaustively chooses a maximum-total-cross-rank dictionary from the 64 possibilities or pairs dominant slots. All rank certificates exceed the theorem's u/128 bound (minimum observed ratio 1/7, not an asymptotic constant claim). 1,536 packed unit grammar decisions match independent factor predictions. No new padding regression; previous proof reused.

120 matching partition contexts with FIXED matching metadata across all of them. For no-cross pairs fix distinct constant patterns, rather than changing tags; 1,353 full-rank pair matrices, 1,964 aligned crossing bits, 261 pair factors with mixed crossing orientations, 960 grammar comparisons. 300 discrete coarea identity checks on random multigraph layouts. 500 random signed AIG attempts produce 447 edge-cut and 306 vertex-separator protocols with nonempty both-side primary sets; verify 13,056 transcript/all-accepting rectangle checks and rank upper bounds with no final output message. These finite protocol checks simulate actual AIG truth tables on all assignments for the tested partitions; no SAT AIG synthesis. All assertions passed. [Replay](packed_welllinked_replay.txt).

The graph obstruction, Menger consequence and geometric bounds are mathematical deductions, not empirical claims about circuit layouts. No actual expander synthesis/routing experiment, Lean verification, production solver change, guarded-slice topology transfer or unrestricted lower bound is claimed.

## 9. Native-agent next steps

Audit the average-rank argument, small-rank acceptance phase, no-output-message rectangle argument, unbalanced counting constants, matching metadata quantifier and graph counterexample; replay the checker. The prior balanced separator theorem follows directly. Formalize the unit grammar and rank/cut simulation in separable pieces if useful. The graph negative control rules out deriving constant-congestion prescribed routing from these cut inequalities alone. To advance distinct-gate accounting, focus on semantic restrictions on internal sharing/operand coordination that go beyond all these cut demands, and use both the graph obstruction and actual sorting/Andreev/cubic controls to falsify overstrong claims. No claim that an arbitrary expander graph realizes a small SAT circuit. L-clb-036 remains open.
