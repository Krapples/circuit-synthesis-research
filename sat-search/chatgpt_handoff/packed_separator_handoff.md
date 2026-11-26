# Packed unit-clause terminal separators and restricted-architecture SAT lower bounds

Date: 2026-11-26. Base [23ba6d4](https://github.com/Krapples/circuit-synthesis-research/commit/23ba6d465525d8ce82d977b81e6cc0062a26e14a). Read [guard_read_normal_form_handoff.md](guard_read_normal_form_handoff.md) first. This round changes the object of accounting from direct primary readers to undirected circuit separators. The paper theorem below gives a linear terminal-separator lower bound for paired SAT, hence quadratic size lower bounds in planar and fixed-minor-free circuit architectures, plus a size/genus and size/crossing tradeoff. The packed unit-clause promise itself admits quasi-linear unrestricted AIGs. Thus L-clb-036 remains open. No literature-priority claim, new Lean theorem, or production solver changes.

## 1. Main statement and model

A circuit graph has a vertex for each physical primary input and each gate, and an undirected edge for each operand wire, ignoring phase, direction and parallel multiplicity for separation purposes. Fan-in at most two, arbitrary fan-out, arbitrary binary gate functions are allowed. Free constants can be treated as public bits or removed; no cost for their vertices is needed. A terminal set T is a subset of the physical primary coordinates, each with weight one; other vertices have weight zero.

**Theorem.** For every sufficiently large even paired SAT word length n, there is a fixed terminal set of cardinality T_n=Theta(n) such that in every circuit correct for SAT at this length, any vertex set C whose deletion leaves components each containing at most 2T_n/3 terminals has |C|=Omega(n).

In fact, for any partition of the circuit vertices into A,B,C with no A--B edges and at least T_n/4 terminals on either side, if |C|<=T_n/256 there is an ordinary constant restriction of primary inputs (chosen after the partition) for which the two-party communication matrix on A and B has real rank >=2^(c T_n) for an absolute c>0. Only designated terminals may be left free; all metadata and all terminals in C are fixed publicly. The restrictions use unit clauses and fixed tautology padding, no copies or negated copies of free physical primary bits. The result is therefore a direct argument about the ORIGINAL circuit graph, not the topology of an auxiliary circuit compiler.

## 2. Packed identifiers with fixed pattern coordinates

Take integer k large, m=2^k slots, ell=floor(k/4), P=2^ell, Q=the least power of two >=(m+1)P, w=log_2 Q+1. All variable IDs

    Q + tag*P + pattern,   tag in {0,...,m}, 0<=pattern<P

have exactly w canonical binary digits. Tags partition the namespace; the ell low digits encode the pattern. IDs are zero-based, as in the repo paired grammar. In particular no ID collision between tags occurs. Let h:{0,1}^ell->{0,1} be a Boolean dictionary chosen as in Section 3.

Emit P unit clauses, one for every pattern p at tag 0, forcing the value of variable Q+p to h(p). Then emit m programmable unit clauses with IDs Q+tag_i*P+x_i and signs s_i, where x_i is an ell-bit pattern. In the paired grammar a unit has [1,sign], w digit pairs [1,d], [0,1], [0,0], length 2w+6. Therefore

    n_k=(P+m)(2w+6)=Theta(k 2^k),
    T_k=m ell=Theta(n_k).

The designated terminals are the ell low-digit payload bits in each of the m slots, each occurring once at a physical coordinate independent of all signs/tags and the dictionary values. Slot i (zero-based) terminal j occurs at zero-based offset (P+i)(2w+6)+3+2j. Signs, high identifier bits, dictionary and delimiters are not designated terminals. This is exactly a literal coordinate restriction, not a nonlocal encoding of a free variable into multiple positions.

Three programmable modes are available:

- Local test: tag_i=0, sign_i=s. Its clause is consistent with the dictionary iff h(x_i)=s.
- Paired inequality: two slots i,j receive the same nonzero tag, unique to that pair, with opposite signs. They are jointly satisfiable iff x_i != x_j, since equality creates opposite unit clauses on the same variable ID.
- Inactive: a slot receives its own unused nonzero tag, and imposes no restriction on its pattern.

These modes can coexist, and the SAT predicate is the product (Boolean conjunction) of the individual local-test and pair-test indicators. The dictionary is forced consistently, all distinct nonzero tags are independent, and no other constraints exist. There are enough tags even if all slots are inactive. This is exact for every assignment of all free pattern bits.

For every sufficiently large even n, use the largest k with n_k<=n-48, then pad with fixed tautology clauses of lengths 10 and 14 (IDs 0 and 1). Every even difference >=48 is a nonnegative integer combination of 10 and 14. The scale ratio n_(k+1)/n_k is bounded eventually, so T_k=Theta(n). Padding has no terminals and does not affect consistency. The actual unpadded packed grammar is replayed below; padding follows the existing handoff argument, not a new replay.

## 3. A shared dictionary with high cross rank on split slots

There exists a single symmetric zero-diagonal ell-by-ell binary matrix R for which every pair of disjoint position sets I,J with |I|,|J|>=ell/8 satisfies

    rank_GF(2)(R[I,J]) > floor(ell/16).

Proof by the probabilistic method: choose each upper-triangle entry independently and uniformly, reflect to the lower triangle. For disjoint I,J the a-by-b cross matrix is uniform independent binary entries, where a=|I|, b=|J|. Set r=floor(ell/16). The number of matrices of rank at most r is bounded by 2^a * 2^(r b) * 2^(r(a-r)): choose a subset of r row indices spanning all rows (pad a basis to r rows if necessary), choose those rows arbitrarily, and express the remaining rows in their span. This upper bound gives probability at most 2^a * 2^(-(a-r)(b-r)) <= 2^ell * 2^(-ell^2/256). There are at most 3^ell disjoint pairs of position sets. The union failure probability is <1 for all sufficiently large ell. Fix any successful R. No efficient deterministic uniform search for such a matrix is needed: the dictionary is a constant restriction of the SAT inputs. One could also choose its contents after seeing the cut; the argument supplies a dictionary working for all such cuts.

Use the quadratic dictionary

    h(x) = XOR_(i<j) R_ij x_i x_j.

Fix other positions arbitrarily. The signed communication matrix on free bits I held by Alice, J held by Bob has entries (-1)^(h(x)). Row and column phase multipliers remove pure-side and linear terms, leaving (-1)^(u^T R[I,J] v). Its real rank is exactly 2^rho, rho=rank_GF(2) R[I,J], because there are 2^rho distinct row characters, mutually orthogonal, and every row is one of them up to phase. If F is the ordinary 0/1 matrix of h=1, then the signed matrix is J_all-ones-2F=(1-F)-F. By rank subadditivity at least one of F,1-F has rank >=2^(rho-1). Choose that sign s for the local unit slot. For sufficiently large ell, log_2 rank>=ell/32. No assumption that every local indicator has full rank, or that the optimal sign is the same across slots, is necessary.

For two slots concentrated on opposite sides, let I be common bit positions with free Alice bits in the first and free Bob bits in the second. Fix every other bit to zero. The paired-inequality communication matrix is J_all-ones - Identity on 2^|I| possible patterns. Its real eigenvalues are 2^|I|-1 (on the all-ones vector) and -1 elsewhere, so for |I|>=1 it has full real rank 2^|I|. This is an exact deterministic communication lower bound, not a randomized communication claim.

For independent factors involving disjoint slots, the conjunction communication matrix is their Kronecker product (up to row/column permutations and repeated irrelevant rows/columns). Real rank multiplies. Thus log rank adds. This is the key reason for using separate unit-clause namespaces rather than counting possible contexts alone.

## 4. Arbitrary balanced terminal cuts: mixed slots or opposite dominant slots

Fix any partition A,B,C of the original circuit vertices with no edge between A and B, each side containing >=T_k/4 terminals. If |C|>T_k/256 we already have the desired separator bound. Otherwise at most T_k/256 terminals are in C. In each slot let a_i,b_i,c_i denote numbers of its ell pattern coordinates in A,B,C.

Discard all slots with c_i>=ell/8. Their number is at most 8|C|/ell<=m/32. Among remaining slots call a slot mixed if a_i,b_i>=ell/8.

Case 1: at least m/32 slots are mixed. Program the local-test mode in all these slots, with independently chosen acceptance sign as in Section 3. Fix each C bit and any other unused input to zero or to the prescribed metadata, except the free A/B bits of the selected slots. Choose all other slots inactive. Each local factor has log rank >=ell/32. The product matrix has log rank >=m ell/1024=T_k/1024.

Case 2: fewer than m/32 mixed slots. Every nondiscarded nonmixed slot is dominated by one side: the other side has <ell/8 bits, and C has <ell/8 bits, so the dominant side has >3ell/4 bits. At most m/16 slots were discarded or mixed, and these contribute at most T_k/16 terminals to either side. The B-dominant slots contribute at most T_k/8 to A. Since A contains >=T_k/4 terminals, A-dominant slots contain at least T_k/16 A terminals, hence there are >=m/16 such slots. Symmetrically there are >=m/16 B-dominant slots.

Pair distinct A-dominant slots with distinct B-dominant slots. For each pair the intersection of their dominant position sets has >ell/2 positions. Program the paired-inequality mode on that pair, leaving just the corresponding common position bits free. All other pattern bits fixed zero, all unused slots inactive. The log rank of each pair is >ell/2, and the log rank of the product is >=T_k/32 (rounding is harmless for sufficiently large m). This case is stronger than needed.

Thus a single fixed set of physical terminals works against EVERY balanced partition, including partitions that split almost all identifiers internally, and the witness-free unit-clause promise supplies the hard restricted communication matrix. The dictionary, tags and signs are allowed to depend on the partition, since the original SAT circuit is correct on all inputs. They are constant and public during the communication protocol. No quantifier exchange assumes a fixed restricted function is hard under all variable partitions.

## 5. Separator simulation with arbitrary internal fanout

Given any circuit vertex partition A,B,C without A--B edges, fix all nonterminal primaries and all C terminals as above. Alice knows the remaining A primaries, Bob the remaining B primaries, and all constants are public.

Process the original circuit in topological order. Both maintain the values of already evaluated C vertices. Gates in A depend only on A and earlier C vertices, so Alice computes them without communication; similarly Bob for B. At a gate in C, exchange the values of its at-most-two operands that come from A or B. Both parties can then evaluate the gate (the gate function and wiring are public). Each C primary is already fixed publicly. At most 2|C| bits suffice for all C gates, independent of fanout. The output party announces the output bit if needed, at cost at most one more bit.

This is a deterministic protocol with a fixed topological schedule and <=2|C|+1 bits. Its accepting transcript rectangles partition the 1-entries of the communication matrix, so real rank is <=2^(2|C|+1) (sum of at most that many rank-one matrices). Combining Sections 4 and 5 yields

    2|C|+1 >= T_k/1024

unless |C|>T_k/256 already. Hence every such balanced cut has |C|=Omega(T_k)=Omega(n). The argument does not assume bounded fanout, a tree, or gate elimination beyond ordinary restriction.

If deletion of C leaves components each containing <=2T_k/3 terminals and |C| is small (<=T_k/256), they can be grouped into sides each containing >=T_k/4 terminals. If some component has weight between T_k/4 and 2T_k/3, take it as one side; the other side has >=T_k/3-|C|>T_k/4. Otherwise greedily accumulate components until reaching T_k/4, overshooting by <T_k/4; the remaining weight is >T_k/4. This proves the main theorem for terminal-balanced vertex separators.

## 6. Topological corollaries and literature

Let s be the gate count and V=n+s+O(1) the vertex count of the original circuit graph. The graph may be simplified by deleting parallel edges; weights remain on the original physical terminals.

**Treewidth.** Every graph of treewidth w has a terminal-weighted separator of size <=w+1: assign each terminal's weight to one bag containing it, select a weighted centroid bag in the decomposition tree, and use the running-intersection property to separate the components. Thus tw=Omega(n), even for unrestricted fanout and all binary bases. This does not imply s is superlinear; sparse expanders have linear treewidth.

**Planarity and fixed excluded minor.** The weighted planar separator theorem of Lipton-Tarjan gives a terminal-balanced separator of size O(sqrt(V)). More generally the classical weighted Alon-Seymour-Thomas theorem supplies one of size O(h^(3/2) sqrt(V)) if K_h is not a minor. Therefore

    s+n = Omega(n^2) for planar or any fixed K_h-minor-free circuit graph.

In particular planar SAT AIGs require Omega(n^2) gates. Under a hypothetical s=O(n^1.01) bound, the graph must contain a clique minor of order Omega(n^0.33) by the classical h-dependent estimate (choose h a sufficiently small constant times n^(0.99/3)). No use is made of recent unreviewed improvements to the separator dependence on h.

**Genus.** The weighted Gilbert-Hutchinson-Tarjan separator theorem gives O(sqrt((g+1)V)) for an orientable genus-g graph. Consequently

    (g+1)(s+n) = Omega(n^2).

For s=O(n^1.01), g=Omega(n^0.99); bounded genus yields a quadratic size bound. This is a bound on the genus of the undirected circuit graph, not the genus of the encoded SAT instance.

**Crossing number.** Draw the original simple circuit graph in the plane in general position with X crossings, and planarize crossings into vertices. There are V+X vertices. Give original terminals weight one, crossings zero. A weighted planar separator has O(sqrt(V+X)) vertices. Convert it into an original-graph separator by retaining original vertices in the separator and replacing every selected crossing with the endpoints of the two original crossing edges (at most four vertices per crossing). Any original path avoiding these removed vertices corresponds to a planarized path avoiding the planarized separator, so each original remaining component has at most 2T_k/3 terminals. The theorem gives

    s+n+X = Omega(n^2).

In particular any drawing of an O(n^1.01)-size SAT circuit has Omega(n^2) crossings. No fixed physical placement, VLSI area, or time-bandwidth model is assumed; this is the ordinary graph crossing number. The argument uses planarization only to obtain a graph separator, not as an electrical circuit simulation.

These are applications of established graph and communication complexity methods, not new separator theorems. References: Lipton and Tarjan, A Separator Theorem for Planar Graphs, https://doi.org/10.1137/0136016; Gilbert, Hutchinson, Tarjan, A Separator Theorem for Graphs of Bounded Genus, https://doi.org/10.1016/0196-6774(84)90019-1; Alon, Seymour, Thomas, A Separator Theorem for Graphs with an Excluded Minor and its Applications, https://web.math.princeton.edu/~nalon/PDFS/spr.pdf. Communication/bisection methods have long been used in VLSI lower bounds, e.g. https://www.cambridge.org/core/books/abs/communication-complexity/networks-communication-and-vlsi/3859E71E921BA29E2A33F87938BB53C7. The specific packing and mixed/dominant cut argument are derived here; no priority claim over related SAT or circuit-graph results.

## 7. Why this is not L-clb-036, and a matching negative control

The entire fixed-width unit-clause promise has O(n log^2 n) signed AIGs. Extract the identifier and polarity records, sort by identifier then sign with a bitonic sorting network, compare neighboring records for equal IDs/opposite signs, and OR their conflict flags. Each record has O(k) bits, there are O(n/k) records, O(log^2 n) compare-exchanges per record and O(k) gates per compare-exchange. Ignore fixed padding. Unit-clause satisfiability is precisely the absence of such a clash. The same upper bound works if dictionary entries, tags and signs vary arbitrarily in that fixed layout. It does not need to know the rank argument or choose a hard restriction. Hence the promise forces linear terminal separator/treewidth and quadratic crossing number for small circuits while itself having quasi-linear general circuits. It is a negative control for trying to turn these architectural requirements directly into an unrestricted gate lower bound.

The result is compatible with the previous two-read compiler. Internal distribution, rather than raw input reads, is the source of the required wide separators. Small circuits can have sparse nonplanar expander-like graphs; no contradiction with a near-linear gate budget has been established.

The topology conclusions apply directly to the physical paired SAT inputs and the original circuit graph at each sufficiently large even length. The guarded Hamming-slice equivalence transfers asymptotic gate exponents through a compiler, but is not known to preserve planarity, genus, crossing number or treewidth. In particular copying/complementing terminals may introduce edges across a cut. No claim of an identical topological lower bound for the guarded monotone graph without an additional topology-preserving reduction. A possible variant is to treat paired rails as one terminal group with explicit identification edges; this is not pursued here.

## 8. Executed finite regression

Run: node packed_separator_check.js. Seed 870019. The checker uses exact GF(2) cross ranks and exact F_101 matrix elimination; a nonzero minor modulo 101 is also a real-rank lower certificate. The character rank identity is checked modulo 101 (orthogonal character norms are powers of two and nonzero in this field); the inequality matrices tested have sizes up to 64 so their constant eigenvalue is nonzero modulo 101.

844 local disjoint-cut character/indicator rank comparisons (ell=3..6), 18 pair-inequality rank checks, 72 slot partition contexts on 32 slots of six bits (192 terminals), 60 satisfying the finite balance thresholds, 54 using mixed local tests, 36 using pairs and 18 using both. Each finite dictionary is sampled until all its selected mixed cuts have positive cross rank; the asymptotic simultaneous rank guarantee is proven separately, not verified exhaustively at large ell. Independent paired grammar unit parser and collision decision matched the factor prediction on 1,296 encoded instances (288 SAT, 1,008 UNSAT). There are 720 exact physical coordinate mutation comparisons under different tag/sign contexts. Largest tested word 3,072 bits. The smallest observed sum of factor log-rank certificates divided by the terminal count was approximately 0.26024 (this is a finite observed quantity, not the asymptotic proof constant). Also 197 sampled disjoint cuts of 24-bit dictionaries, minimum observed cross rank 3; not a universal guarantee. All assertions in the final checker passed. [Actual replay](packed_separator_replay.txt).

Two preliminary script attempts failed (one syntax error; one planted positive case incorrectly left the partner pattern random). The final checker sets both patterns of each planted pair to distinct values and passes. No AIG synthesis, graph separator enumeration, genus or crossing computation, Lean verification, or new padding/slice replay was executed; graph consequences follow from the paper proof and cited separator theorems. No literature-priority claim.

## 9. Next milestone

The new target is more concrete: a hypothetical small SAT circuit must have a large well-connected terminal core. We can study lower bounds on the computational work inside such cores, perhaps via multiple cut protocols sharing stable internal gate IDs. But one must not sum communication demands across cuts without bounding their overlap, as the unit-clause sort control already falsifies a naive argument. The hard part is to distinguish a small routing circuit that handles variable-ID collision detection from a circuit that also handles arbitrary shared existential constraints.

Native agent: independently audit the rank union bound, physical coordinate layout, mixed/dominant split, communication simulation and padding; replay the checker. If useful formalize the unit namespace semantics and separator protocol in existing Lean grammar/circuit libraries. The classical graph separator theorems can remain explicit external premises. Compare to prior residual-family saturation and routing controls; do not claim a full SAT gate lower bound or use this as a production topology filter without proof/differential validation. L-clb-036 remains open.
