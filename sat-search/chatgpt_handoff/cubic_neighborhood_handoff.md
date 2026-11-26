# Connected cubic witnesses: neighborhood kernels and low-dimensional marginal circuits

Date: 2026-11-26. Base handoff [56c61b1](https://github.com/Krapples/circuit-synthesis-research/commit/56c61b1a906230f9bb872d7a2a7ff5a02ce2aa02). Read [cubic_component_handoff.md](cubic_component_handoff.md) first. This round removes the independent-component hypothesis for the structural kernel, using graph-separated neighborhoods and conditional independence. It gives a deterministic quasi-linear circuit upper bound for two new specified connected cubic subpromises, not all cubic maps or unrestricted SAT. L-clb-036 remains open. The algebraic algorithm has finite replay; the asymptotic circuit construction remains paper mathematics.

## 1. Setting and theorem

Let F: GF(2)^q -> GF(2)^k be a degree-at-most-three multilinear Boolean map written as

    F(x) = b XOR sum_(nonempty A, |A|<=3) c_A product_(i in A) x_i,

where c_A is a k-bit coefficient label and zero labels are omitted. Cancel equal monomials first (XOR their labels); repetitions of a variable within one monomial are removed. The interaction graph G has the q variables as vertices, with an edge whenever two distinct variables occur together in a nonzero monomial. Let Delta be its maximum degree. The raw pre-cancellation graph may be used as an overestimate for separation and degree. All bounds on Delta refer to a specified upper bound, not an assumption that sparsity implies bounded degree.

**Theorem.** There is a deterministic algorithm selecting a set K of at most

    8 k^2 (1 + Delta + Delta^2 + Delta^3)

original variables such that

    image(F restricted by x_i=0 for i outside K) = image(F).

This is an actual coordinate kernel, not a general linear sketch, and does not assume independent components, bounded treewidth, or a small supplied separator. A connected bounded-degree expander is covered by the structural theorem. No claim is made that computing the exact image of the kernel is always quasi-linear.

More precisely the algorithm produces a dual subspace Lambda of dimension t<=k such that both original and compressed image equal the inverse image of the same marginal image under projection by any basis of Lambda. The marginal depends only on K. When t=0 the image is all GF(2)^k.

## 2. Constructing separated neighborhoods by residual label span

For a vertex v let N[v] be its closed radius-one neighborhood in G; let B_3(v) be its closed radius-three ball. Start with all vertices alive and K empty. Run R=8k rounds, each starting with an empty basis of GF(2)^k.

Within a round, repeatedly find a nonempty monomial A which has some alive vertex v in A and whose coefficient c_A is not in the span of the round's basis. Insert c_A into the basis, record the center v with its label c_A, and mark all vertices in B_3(v) dead, adding them to K. End the round when no such monomial remains. There are at most k selections per round. Use any deterministic ordering to break ties.

After the rounds let V be the span of all labels of monomials containing at least one still-alive vertex. Set Lambda=V^perp. The following properties hold.

1. Distinct selected centers have graph distance at least four, including distance infinity in distinct components. Thus the closed neighborhoods N[v] are disjoint and have no edges between them: an inter-neighborhood edge would give a path of length <=3 between the centers. No monomial meets two such neighborhoods.
2. Every selected neighborhood is inside K. A radius-three ball has at most 1+Delta+Delta^2+Delta^3 vertices. Hence the stated kernel bound.
3. If lambda lies outside Lambda, at least one final residual label has nonzero dot product with lambda. That label was eligible (had an alive vertex) at the end of each earlier round. Each round's basis spans every label eligible at its end, by termination of the greedy loop. Consequently each of the R rounds selected some center-label pair (v,c_A) with lambda dot c_A=1. These give R distinct separated neighborhoods.
4. If lambda lies in Lambda, every nonconstant monomial of the scalar polynomial lambda dot F has all its variables in K. Otherwise its label was among the final residual labels and would have dot product zero. In particular the Lambda-marginal is unchanged pointwise when coordinates outside K are set to zero. Constant terms are also preserved.

No linear-algebra premise beyond ordinary basis insertion is needed.

## 3. Conditional bias lemma for neighborhoods

For any lambda outside Lambda, select one of its witnessing center-label pairs per round as in property 3. Write P=lambda dot F. Condition on arbitrary values of all variables outside the union of these R closed neighborhoods. The conditional scalar polynomial is a sum of polynomials on disjoint neighborhood variable sets, plus a constant, since no monomial meets two neighborhoods.

Each neighborhood polynomial is nonconstant for EVERY outside assignment. Indeed its chosen monomial A contains the center v. Every monomial of F containing v is wholly inside N[v] by the definition of the interaction graph. Thus conditioning cannot alter the coefficient of A: any additional original monomial that could become A after fixing outside variables would also contain v and would already be wholly inside N[v]. The coefficient lambda dot c_A=1 remains. This argument requires actual canceled coefficients (or a canonical coefficient representation), not a nonzero raw occurrence that cancels.

A nonconstant degree-at-most-three Boolean polynomial has density of both zero and one at least 1/8 by the elementary minimum-weight bound from the previous handoffs. Therefore the magnitude of its signed bias is at most 3/4. Independence of the uniform neighborhood bits conditional on all outside bits makes biases multiply. Averaging over the outside assignments gives

    |E_x (-1)^(lambda dot F(x))| <= (3/4)^R.

The same inequality holds for the coordinate-restricted map F_K: every witnessing neighborhood remains entirely free, and setting other variables to zero is just one more outside assignment. No unconditional independence of graph neighborhoods is asserted. This works for dense overlapping monomials within a neighborhood and for connected graphs, including those with cycles.

## 4. Fourier marginal lifting and exact image

Let t=dim Lambda and pi(a)=(lambda_1 dot a,...,lambda_t dot a) for a basis of Lambda. By property 4, pi(F) and pi(F_K) have the same distribution under uniform original and retained variables. Fix an address a.

If pi(a) is not attained, neither map attains a. Otherwise the marginal fiber indicator is a nonzero Boolean polynomial of degree <=3t, so its uniform probability p is >=2^(-3t). For either map H, Fourier inversion gives

    2^k Pr[H=a]
       = sum_(lambda in Lambda) (-1)^(lambda dot a) beta_H(lambda)
         + sum_(lambda outside Lambda) (-1)^(lambda dot a) beta_H(lambda),

where beta_H(lambda)=E[(-1)^(lambda dot H)]. The first sum is 2^t p>=2^(-2t)>=2^(-2k), by Fourier inversion on the marginal. The magnitude of the second sum is at most 2^k (3/4)^(8k)<2^(-2k) for k>=1, since (3/4)^8<1/8. Hence both maps attain a. This proves

    image(F) = image(F_K) = pi^(-1)(image(pi(F_K))).

The theorem preserves support, not the original histogram. The proof works for any fixed degree D>=2 by replacing 3/4 with 1-2^(1-D), and choosing R=O_D(k) such that that bias to power R is <2^(-Dk). The radius-three graph construction still works because each monomial induces a clique. Degree one has an ordinary span kernel. The cubic constant 8 is sufficient but not optimized.

## 5. Explicit circuit cost of the kernel construction

Given q variable IDs and m monomial records (fixed degree), the above deterministic selection and compressed coefficient routing can be implemented in (q+m+1) poly(k,log(q+m+2)) bounded-fan-in Boolean gates, even without the degree bound. The degree bound is used for the size of the resulting kernel. Here are fixed-array details; these are not measurements.

- Canonicalize each monomial by sorting its at-most-three IDs, removing duplicates, then sort the m records by the canonical key. Segmented XOR yields actual coefficient labels. Store the aggregate at a representative and mark remaining records inactive. Build an edge list of at most 3m undirected edges from active terms of size at most three. Constant terms are stored separately. This takes O((q+m+1) poly(k,log(q+m+2))) gates by sorting networks and segmented scans; compare-exchanges on records of poly(k,log(q+m+2)) bits have polynomial cost in that width.
- Use R rounds of exactly k pivot slots (dummy slots if no selection is possible). Route alive flags to the at-most-three queried IDs per term by sorting a vertex-record table together with queries and copying along equal-key runs. Compute for each term its reduced label against the current k-bit basis (unrolled elimination, O(k^2) gates per record), and its candidate alive vertex if any. A first-valid prefix scan and masked OR obtains the first eligible record and its selected center ID. Update the small basis if valid.
- To mark a radius-three ball, start a vertex frontier at the selected center using equality of IDs, then run exactly three synchronous graph propagation passes. In each pass route endpoint frontier flags to edge records, OR them into neighbor flags by sorting and segmented OR, and retain old flags. A dummy center generates no frontier. OR the final flags into K and update alive. This uses O(q+m) records of polylogarithmic bit width, with no adjacency lists of input-dependent capacity or unit-cost RAM.
- After Rk pivot slots, form the final residual coefficient basis by an unrolled scan; obtain a basis of its orthogonal complement by ordinary elimination on a k-by-k matrix. Route retained flags to monomials, zero terms having any unretained variable, and assign each retained variable a consecutive local ID by prefix counts. Route local IDs back to retained records.
- For a promised Delta bound, define K_max=min(q,8k^2(1+Delta+Delta^2+Delta^3)). One can collect a dense fixed-size array of all <=3-subsets of local IDs, with a k-bit coefficient per key, by sorting and segmented XOR; alternatively scan every source record separately for each possible local key. The latter costs O((q+m+1) poly(k)) when Delta is constant or poly(k). The array has O(K_max^3) entries, including zeros and a constant slot. A masked invalid-record convention handles padding. No variable-size output or hidden random-access cost is required.

The packed cubic encoding from the previous handoff has q<=m=O(M/k), M=2^k, length n=Theta(M). Its raw monomials are directly extracted from fixed positions, with row coefficient label from the logical permutation and constant b from the source parities. Consequently for constant or polylogarithmic Delta the compressed coefficients and marginal basis are constructible by deterministic O(n log^C n) gates for a fixed C. The full exact kernel image can be evaluated by enumerating at most 2^K_max assignments, but that bound is generally too large. With constant Delta the kernel has O(k^2) variables, a quasipolynomial full-enumeration upper bound, not a quasi-linear result by itself.

## 6. New deterministic near-linear subpromises

The marginal lifting theorem is stronger than mere kernel existence: only t output bits must be solved on the retained variables.

### A. Low residual marginal dimension

Any attained marginal address has a witness supported on at most 3t retained variables. Proof: its indicator polynomial is nonzero of degree <=3t. Choose an inclusion-minimal monomial with coefficient 1, set its variables to one and all others to zero; the result is one because no proper subset has coefficient 1. Thus enumerate only subsets of K_max positions of size <=3t, evaluate the marginal and retain its attained keys. This is deterministic and exact.

For circuits use a fixed promise t<=t_max. Allocate all subsets of size <=3t_max, including the empty set, at compile time. Their number is at most (K_max+1)^(3t_max) (encode subsets as sorted padded tuples of length 3t_max). For t_max=0 there is exactly one assignment. Each evaluation costs poly(k,K_max) gates using the dense compressed coefficients. Encode each t-bit marginal key into a fixed k-bit padded key (zero unused basis rows), and route the length-M list of address queries pi(a) against the enumerated keys via sorting and segmented OR. AND the returned flags with h[a] and OR them. This adds (M+(K_max+1)^(3t_max)) poly(k,log(q+m+2)) gates.

In particular if Delta=poly(k) and

    3 t_max log_2(K_max+1) <= k,

the entire variable-incidence promise is decidable by deterministic O(n log^C n) AIG gates. For constant Delta the permitted t_max is Theta(k/log k) asymptotically (approximately k/(6 log_2 k) ignoring constant factors). For Delta<=k^a with fixed a, the analogous threshold is also Theta(k/log k). This is a significant regime beyond t=O(1). If the inequality fails, this particular argument may cost more than quasi-linear. The promise can be checked by the algorithm, but a general circuit correct on all inputs is not obtained by treating failure as UNSAT.

### B. Quadratic residual marginal, possibly high t

Suppose all degree-three coefficient labels of the original map lie in V, the final residual label span. Equivalently every scalar polynomial from Lambda has degree <=2, since Lambda=V^perp. This condition is checkable on the canonical coefficients. Then pi(F_K) is a quadratic map on at most K_max=poly(k) variables, even though the original graph may be connected and its degree-three part extensive.

Apply the earlier exact quadratic character-sum and Walsh algorithm directly on the compressed variables: each of at most 2^t<=M scalar sums costs poly(k,K_max) gates by pair elimination, then one integer Walsh transform recovers the support. Use a fixed k-bit padded marginal map if t varies (zero extra rows) to avoid dynamically sized transform arrays; length M remains valid. Counts and intermediate arithmetic have O(K_max+k)=poly(k) bits, so O(M poly(k)) gate cost. No invocation of the earlier deterministic sparse quadratic compression theorem is necessary here. It is the elementary dense quadratic elimination algorithm on a small kernel.

Thus this second connected cubic subpromise also has deterministic O(n log^C n) circuits, even if the residual marginal has dimension Theta(k). In particular the kernel method handles systems with global cubic mixing in the high directions and a large but quadratic exceptional marginal.

A further parameterized case: if a supplied set of s retained variables hits all nonzero cubic monomials of the Lambda-marginal, enumerate its 2^s assignments and run the quadratic marginal algorithm for each, ORing the supports. Conditioning removes at least one variable from every cubic monomial, so the residual marginal is quadratic. Total O(2^s n log^C n) gates. If s=O(log log n) this is quasi-linear; if s<=epsilon log_2 n with fixed epsilon<0.01 it remains o(n^1.01). Finding such a hitting set efficiently is not claimed.

These conditions are sufficient, not necessary, for small circuits. A large connected core alone is not enough to evade compression. Remaining cases include growing degree, large nonquadratic residual marginal and no small supplied hitting set. The kernel theorem does not itself give a lower bound on any of them.

## 7. Executed replay and limits

Run from this directory: node cubic_neighborhood_check.js. Seed 870012. The actual committed source was executed in a JS runtime. The checker canonicalizes coefficients, computes the separated-neighborhood kernel, verifies neighborhood separation and the residual marginal pointwise support condition, then independently checks exact histograms. Small arbitrary hypergraphs use exhaustive enumeration; long connected path hypergraphs use an independent transfer-matrix dynamic program with the last two bits and address as state, using exact BigInt counts (not floating-point probabilities). Both the original map and its zero-restricted map are checked. The test also explicitly checks the rational bias bound using integer arithmetic and low-weight marginal enumeration.

Actual [output](cubic_neighborhood_replay.txt): 150 small maps, 14 connected paths of 2,300 variables, 30 strict reductions, 3,518 address-support/marginal-lift checks, 674 scalar bias checks, 164 low-marginal image comparisons. 102 maps have full image. Maximum graph degree across all tests 9; maximum retained count 2,016; largest discarded count 2,188. In the largest-discard example q=2300, k=2, Delta=4, retained 112, marginal dimension 1, and all four addresses attained. The planted path family also includes two-dimensional non-surjective marginals (three of four marginal addresses possible), so not all connected tests are trivially surjective. All assertions passed.

The long connected tests have path structure for independent exact verification; they do not empirically benchmark expanders or arbitrary large connected graphs. The theorem is proved for general graph structure under the degree hypothesis; only its finite checks are restricted. No actual AIG synthesis or Lean verification. The cubic exact paired-grammar replay from the previous handoff remains outstanding. Do not confuse abstract polynomial verification with SAT grammar verification. No literature-priority claim; related background on low-degree equations includes https://theoryofcomputing.org/articles/v009a027/ and the earlier cubic bias structure references. The proof above uses only the elementary minimum-weight bound and Fourier inversion, not an external cubic regularity theorem.

## 8. Native-agent next steps

- Audit the separation radius, conditional nonconstant monomial argument, and Fourier marginal-lifting proof. Replay the checker; independently validate the fixed-array sorting and propagation cost.
- Keep the earlier deterministic quadratic sparse rank gate-cost proof under review; this round's quadratic-marginal bound uses dense pair elimination and does not depend on that earlier sparse rank result.
- Extend the quadratic Python grammar checker to actual cubic clauses and exact paired positions/balancing/padding, as previously requested.
- Investigate high-degree witness hubs, bounded-degree expanders with high-dimensional cubic exceptional marginal, and whether the residual cubic coefficients admit further input-dependent compression. A useful falsifiable goal is to reduce the dimension of the exceptional marginal or find a small cubic-monomial hitting set without assuming it supplied.
- To advance L-clb-036, a genuinely new lower-bound bridge is still required: path multiplicity, cubic counting hardness, and kernel size are not distinct-gate lower bounds. No production solver or verified Lean library changes. L-clb-036 remains open.
