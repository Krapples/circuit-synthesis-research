# Causal response-table cuts and an additive weighted gate charge

Date: 2026-11-26. Base [811266b](https://github.com/Krapples/circuit-synthesis-research/commit/811266b4e5ea603d7937dc50247851d3995a69f1). Read [packed_directional_handoff.md](packed_directional_handoff.md) first. This round supplies a stronger topology-sensitive invariant than directional port counts alone. The proof gives a virtual capacitated flow on one side of the original DAG and an additive inverse-capacity gate charge. It also constructs enabled permutable packed lookup inputs with injective residuals across metadata contexts even when only one group is active. These are paper theorems and finite regression, not a new unrestricted superlinear size bound, Lean theorem, or literature-priority claim. L-clb-036 remains open.

## 1. Response functions attached to actual original vertices

Let C be a Boolean circuit DAG, with arbitrary finite fanout and fan-in at most two (the cut lemma itself also works for arbitrary Boolean gates). Partition original vertices into A and B, with output owned by B. Let S be a set of free data primary bits in A and fix every other A primary to public constants. Bob's input is the remaining B primaries, with any desired domain restriction. Additional B primaries may be fixed publicly. The forward ports F are A vertices having a reader in B; reverse ports R are B vertices having a reader in A. Use distinct source vertices, not operand occurrences.

For each v in A define:
- D(v) = the subset of S with a directed path to v staying entirely in A, including length-zero paths.
- R(v) = the reverse-port vertices u in R with an edge into an A vertex that has a directed A-only path to v (including length zero after the first edge).

Compute these sets by unions in topological order on A: at a primary initialize its own data bit if present; at a gate union its A predecessors' sets and add any direct B operands to R(v). These are syntactic supports; they may overestimate actual dependence. In particular R(v) is NOT the full set of B ancestors allowing arbitrary repeated boundary crossings.

For fixed assignment x of S, break every B-to-A edge and instead treat the reverse port values as independent formal parameters. A's local computation becomes an acyclic Boolean circuit. At vertex v this defines a response function

    T_v(x): {0,1}^R(v) -> {0,1}.

There are at most 2^(2^|R(v)|) possible response functions, and the table depends on x only via D(v) (other A primaries are fixed). Therefore as x varies the number of possible tables at v is at most 2^c(v), where

    c(v) = min(|D(v)|, 2^|R(v)|).

A vertex with no free local data ancestors has c(v)=0, even if its value depends on incoming feedback. A vertex not reached locally by any feedback has c(v)<=1, regardless of how many data ancestors it has. A data primary has capacity 1. These capacities describe the logarithm of the number of possible response tables, NOT the number of independent bits carried by the vertex in one actual circuit evaluation. We do not assume reverse-port values are jointly attainable or independent in an actual execution.

## 2. Causal response-cut theorem

Let K be ANY subset of A vertices meeting every A-only directed path from S to F, including length-zero paths if a data primary itself is a port. Let N be the number of distinct residual functions f(x, .) on Bob's allowed input domain, as x ranges over all data assignments.

**Theorem.**

    log_2 N <= sum_(v in K) c(v).

Proof: encode x by the vector of response tables T_v(x) for v in K. The code has at most 2^(sum c(v)) distinct possibilities, by the independent upper bounds on the number of possibilities per component. No independence of the actual tables is needed. We claim this code determines the entire residual function on Bob's domain. For any allowed Bob input y, simulate the original circuit in its topological order. In evaluating each forward port, use the local A sub-DAG recursively, stopping on a K vertex, a B operand, or a primary. At a K vertex, evaluate its encoded response table at the values of its actual earlier reverse-port ancestors R(v). Every such reverse vertex precedes v in the original DAG, so it is already evaluated by the time the forward port is needed. At a B operand use the already computed B value. At a primary outside K, the recursive evaluation cannot reach a free S bit: the corresponding path to the forward port would avoid K. Hence every such primary is publicly fixed. All returned port values are the correct ones by topological induction. In B compute gates locally using these earlier port values and y. The output is in B, so this reconstructs f(x,y). Equivalently, one can run the entire circuit with a dummy S assignment and override K vertices by their encoded response values; the A-only cut ensures no incorrect dummy-data value can affect F before hitting K. Thus two x with identical codes have identical residuals, proving the inequality.

This is a genuine strengthening of the preceding global strategy count a*2^b>=log N. Taking K=F gives sum_(v in F) min(|D(v)|,2^|R(v)|) <= |F|*2^|R|. Earlier ports with fewer feedback ancestors are charged less. Taking K INSIDE A further accounts for irreversible compression of data before later feedback arrives. The bound is valid for ANY K simultaneously, not just layers or topological prefixes. It also applies after fixing any subset of S to constants: recompute D relative to the remaining varying bits and use the corresponding residual count. Choosing constants can change N; the syntactic capacity remains an upper bound. If output is on A, the conclusion does not in general hold unless that output is included as an additional forward port (or moved into B with an explicit interface). The output-owner premise matters.

### Two explicit strict separations from the older tests

Let M=2^k, k>=4. Form a graph of an actual AIG on M data bits in A and k query bits in B. Partition the data into k nonempty balanced groups, compress each group in A into one parity signal z_i, then form forward signals w_i and combine their XOR or AND on B. Every input is an ancestor of output; this is NOT an AIG computing INDEX, but a candidate topology to be ruled out for that target.

- Local-feedback variant: w_i=z_i XOR q_i. There are exactly a=b=k distinct ports. All older INDEX directional bounds pass, including a*2^b>=M, and log-rank requirement a+b>=k. Yet each forward port has only one local reverse ancestor, so total causal capacity at F is 2k<M. The new theorem rules out this topology for INDEX.
- All-feedback variant: compute g=parity(q_1,...,q_k) in A, and w_i=z_i XOR g. Again a=b=k and all earlier bounds pass. Each forward port has ALL k reverse ancestors; the total capacity at F is M (data groups partition the inputs), so even the refined port test passes. But K={z_i} cuts all local data-to-port paths before feedback reaches them, and sum c(v)=k<M. Thus the internal-cut theorem rules out this topology too.

These are structural impossibility statements, based on the actual connections and syntactic dependencies; changing the truth functions of the gates while preserving the topology cannot make it compute INDEX. The XOR and AND choices are merely explicit AIG realizations of those topologies. For k=4 the respective causal capacity pairs (F,K) are (8,4) and (16,4), while 16 bits are required. Do not confuse a candidate topology with a correct lookup circuit.

## 3. From cuts to a weighted additive distinct-gate bound

There is a useful flow formulation of the causal-cut theorem. Consider the directed graph induced by A. Give each vertex capacity c(v) (including source and sink vertices). Join a supersource to every S primary, and every F vertex to a supersink with effectively infinite capacity, say |S|+1. Give original directed A wires capacity |S|+1. Split vertices into in/out nodes with an edge of capacity c(v) to use ordinary max-flow/min-cut. Cutting all S primary capacities costs |S|, so a minimum cut never needs an effectively infinite edge. Its finite crossing edges give a vertex set meeting every S-to-F path. Conversely any such vertex cut yields a network cut of at most its summed capacity. By the theorem and max-flow/min-cut, there exists an integral flow of value at least ceil(log_2 N). This is a VIRTUAL flow of data degrees of freedom to response-table slots, NOT a simultaneous physical transmission of these bits on the original one-bit wires.

In particular if x -> f(x,.) is injective, N=2^|S|, and the maximum flow value is exactly |S|. Each source primary has capacity one, hence the acyclic integral flow decomposes into one unit path P_i for each data primary i. A gate v is visited by at most c(v) paths. Define a path's weight to be the sum of 1/c(v) over its A gate vertices (exclude primary inputs; include a forward gate endpoint). Only positive-capacity vertices can carry flow. Define d_i as the minimum such weight over all directed A-only paths from i to a forward port through positive-capacity vertices, allowing a length-zero path when i is a forward port.

**Additive gate charge.** If the residual map is injective,

    s_A >= sum_(i in S) d_i.

Proof: sum the weights of the integral paths. For each actual A gate v, the total contribution is load(v)/c(v)<=1. Thus sum_i d_i <= sum_i weight(P_i) <= s_A. This counts distinct gates rather than adding overlapping subcircuit sizes. The shortest-path distances can be computed by a backwards DAG dynamic program after computing the capacities. More generally for N not a power of two corresponding to all bits, choose ceil(log_2 N) distinct flow sources; the bound then uses the sum of that many smallest source distances, since source identities are not prescribed.

A direct restricted-architecture corollary: if every data-to-forward-port path visits at least L A gates with |R(v)|<=h, then d_i>=L/2^h for every data bit, and

    s_A >= |S| L / 2^h

under residual injectivity. In particular, a long compulsory pre-feedback computation on independent data requires many actual gates; a deep region cannot first collapse many independent table bits into a small number of one-bit signals and recover those bits by receiving later queries. The condition is on ALL relevant directed paths, not on maximum path length, a chosen long path, or unfolded formula multiplicity. If all data bits can be forwarded directly or feedback reaches gates early, d_i can be small and the bound does not yield superlinear size.

This is the promised sound charge beyond the previous ingress count ledger: capacities now depend on actual gate/operand ancestry. It is still not a proof that a superlinear value of the charge is forced for SAT. The need for such a proof is a new concrete target. This is distinct from the prior multicommodity routing question: these paths are single-commodity, unprescribed destinations, and can have virtual capacity greater than one at a vertex. No coding-to-constant-congestion physical routing implication is claimed.

## 4. Enabled permutable packed lookup grammar: joint residual injectivity

Extend the preceding packed batched lookup construction. As before M=2^k, ell the largest power of two <=max(1,floor(k/2)), P=2^ell, B0=M/ell, lo=log_2 ell. (B0 is a block count, distinct from circuit region B.) There are r logical groups. In each group add an enable variable e_j pinned by one unit polarity E_j. The data clause for logical block i becomes

    (-e_j OR -guard_(j,i) OR V_(j,p)).

With E_j=0 every data clause in the group is inactive; with E_j=1 the usual selected table bit must be one. Emit all fixed group address/enable unit clauses, guard tree clauses and dictionary clauses first. Then emit r B0 physical data slots in fixed order, allowing any permutation pi of the logical (group,block) labels. In physical slot h, use the enable and guard identifiers of logical label pi(h), and the V variable from its logical group, with low ell digits equal to physical payload p_h. Metadata programs the mapping without changing the positions of data bits.

Exact namespace: allocate rP dictionary IDs Q+jP+p, then A0=r(k+2B0) auxiliary IDs Q+rP,...,Q+rP+A0-1, Q least power of two >=rP+A0. All have common canonical width w=log2 Q+1. The auxiliary count includes k address variables, one enable and 2B0-1 guard nodes per group. Data clause low pattern digit t occurs at offset 2(2w+4)+3+2t from the start of its clause, independently of pi. The enable and query sign bits also each occur once at invariant coordinates. This proves the layout is a single-copy restriction, not a copied primary projection. As in the preceding handoff, r<=M^c fixed c gives word length Theta(rM) for large k. Fixed r=2^floor(gamma*k) and prior 10/14 tautology padding extend to all sufficiently large even lengths. This round reuses the padding argument, rather than replaying padding or balancing.

The exact SAT predicate is

    F_pi(H,q,E)= AND_j (NOT E_j OR H_(pi^-1(j B0+floor(q_j/ell)), q_j mod ell)),

where H lists the physical chunk payloads. Under any fixed pi, if all data bits lie in A and all query/enable bits lie in B, the residual map of the rM data bits into functions of q,E is injective: enable only the group and choose the address of any desired bit. Thus even an all-zero table is distinguishable from every other table, unlike the unenabled AND of lookups, where all-zero groups collapse the residual to zero. The causal-cut theorem then charges rM independent data bits rather than r(M-1) sentinel-fixed bits or log of the number of nonempty Cartesian products.

### Stronger multi-context variant with a SINGLE active group

Fix E_0=1 and all other enables zero. Fix high query bits of group 0 to zero and all other groups' queries to zero. Allow only its lo low query bits and programmable permutation metadata to vary. For every physical chunk h there is a permutation taking h to logical slot (group 0,block 0), e.g. by swapping that chunk with the current occupant. Then for each bit position t choose q_0=t. The output equals that one physical data bit H_(h,t). Consequently the JOINT residual map across the allowed metadata and low-query inputs is injective on all rM data bits, even though each separate fixed metadata context reads only one ell-bit chunk. This statement needs the metadata coordinates that vary across the chosen contexts to lie in B, and the varying low query bits in B; all other A inputs must be the SAME public constants across the contexts. If these metadata bits are on A and fixed differently in different contexts, one cannot assert a single joint code or simply sum the per-context bounds. Bob's domain need not be a full subcube: it consists only of legal programmed permutations and query values. The general causal response theorem allows this.

This is a concrete way of making the same cut response tables account for many context-specific uses. If all data bits are in A and output is in B under the stated domain, every internal causal cut must have capacity >=rM and the additive charge applies to all rM sources simultaneously. No assumption that one slot's computational path is distinct in all contexts is made. The total information demand is still bounded by the input data length, and weights may become tiny when metadata feedback reaches a gate. The proof does not establish a superlinear numerical lower bound for arbitrary SAT circuits.

### Small-circuit negative control

The entire enabled permutable promise admits O(n log^2 n) signed AIGs: extract records containing the common-width guard ID and the ell-bit payload of each physical slot, sort by guard ID with a bitonic network, then evaluate each ordered logical group's ordinary mux tree and enable implication, and AND the results. Guard leaf IDs increase with logical block order within a group and group namespaces occur in increasing order. All compare-exchanges act on O(log(rM)) bits and there are O((rM/ell) log^2(rM)) of them. For fixed pi the sorting is unnecessary, giving O(n) gates. Thus even joint residual injection across programmable metadata does not alone force a superlinear gate exponent. It is the combination with an unavoidable causal path-cost property that could potentially yield a distinct-gate advance. No such property has been proved.

## 5. Executed regressions

Run in this directory:

    node causal_response_check.js
    node causal_lookup_check.js

Causal response checker, seed 870022: 213 random signed AIGs (random region assignments, Bob-owned output), 42 actual mux AIGs, 777 data subsets, 4,428 internal cut tests, 60,492 data-to-response code checks, 438,712 direct comparisons with reconstruction from cut tables over all tested Bob inputs, 57,368 distinct response codes counted across cuts. The checker explicitly simulates hypothetical independently supplied reverse-port values, computes the per-cut tables, then reconstructs the full circuit with dummy data and table overrides. All tests compare actual residual truth tables, not merely syntactic capacities. In 664 of the tested source-subset cases the refined port capacity was below the older global strategy bound; in 658 cut tests the internal bound was below the corresponding refined port capacity. These counts compare upper capacity estimates, not strict lower-bound improvements for minimum AIG sizes. The eight explicit rejecting topologies for k=4..7 (two variants each) have actual directed cuts and pass the earlier global numerical inequalities; the local variant fails at ports and the all-feedback variant only fails the new internal-cut test. 777 vertex-split max-flow/min-cut certificates checked, with 513 full-source flows and corresponding additive gate-charge tests; maximum observed weighted charge 21. These tests of full flow also include cases with noninjective residuals where flow happens to be full; the graph charge remains valid for such a full flow. No optimum synthesis or claimed asymptotic gate-count improvement. [Replay](causal_response_replay.txt).

Enabled lookup checker, seed 870023: 72 primary cases, 42 SAT and 30 UNSAT, 72 changed-permutation layout/semantic checks, 216 single-bit coordinate mutations (data/query/enable), 216 individually programmed data retrievals and another 216 using a SINGLE fixed active group, changing only its low query and permutation metadata. Exhaustive joint residual check at three small configurations: 336 distinct data rows total, 2,496 residual entries with arbitrary group selection, 336 distinct rows and 2,496 entries again for the one-active-group metadata case. Independent token parser and unit propagation used throughout. Largest tested word 55,056 bits, max data 256 bits. Added single-group probes consume random draws, hence final SAT/UNSAT counts differ from preliminary replay; committed replay is the final one. [Replay](causal_lookup_replay.txt).

Both final scripts passed all assertions. These checks cover arbitrary feedback on small DAGs, real packed bit layouts, causal flow certificates, and strict topology rejections. They do not verify every possible circuit or prove the asymptotic theorem; the above proof supplies that general argument. No new padding/slice replay, general SAT AIG synthesis, actual expander routing, Lean verification or production solver modification.

## 6. Relation to existing methods and next target

This follows the classical communication strategy encoding and asymmetric communication framework (Miltersen, Nisan, Safra and Wigderson, On Data Structures and Asymmetric Communication Complexity, https://doi.org/10.1145/225058.225093, https://www.brics.dk/RS/94/41/), and uses ordinary max-flow/min-cut and shortest-path charging. It is a self-contained specialization to local feedback cones and arbitrary internal cuts in a circuit DAG. No literature-priority claim for this type of strategy table or flow inequality. General network coding and multicommodity flow issues remain separate; we use no claim that cut capacity implies constant-congestion prescribed-pair routing.

Concrete research target: for a hypothetical near-linear SAT circuit choose a legal partition with many packed data bits on one side and suitable query/metadata bits on the other, then use the actual graph to prove a LARGE SUM of inverse-capacity shortest path distances. The challenge is to force long positive-weight paths despite early feedback, direct forward ports, and the fixed topology's ability to sort/reroute metadata. A stronger refinement could restrict local response functions to actual compatible feedback histories or exploit constraints on their joint realizability by the same original gates. Such refinements must remain sound even when feedback depends on the data and earlier messages. Do not identify response-table entries with independent physical gate outputs. Do not sum charges over overlapping partitions unless a separate per-original-gate capacity proof justifies it.

Native agent: independently audit the reconstruction lemma (especially reverse ports dependent on earlier data messages), min-cut/flow argument, inverse-capacity metric, and enabled permutable grammar with the one-active-group quantifier. Replay both checkers. The theorem is a possible topology-sensitive rejection filter on a specified graph, not an established stronger numerical minimum-size bound on arbitrary SAT. Keep experimental until proof and differential audit. No production integration or priority claim. L-clb-036 remains open.
