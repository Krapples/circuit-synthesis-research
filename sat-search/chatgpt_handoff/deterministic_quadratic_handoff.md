# Deterministic quadratic image compression via orthogonal blocks

Date: 2026-11-26. Base handoff: afe375378fd0d7d9ab390cc311ca4264b5b1f576. The latest README and quadratic_compression_handoff.md were inspected. No independent native-agent audit of this round has occurred. L-clb-036 remains open.

**New paper theorem, with executed finite algorithm tests:** a sparse quadratic map F: GF(2)^q -> GF(2)^k admits a deterministically constructed *linear* subspace E of dimension O(k^4) with F(E)=F(GF(2)^q). The construction can be implemented by binary Boolean circuits of size (q+m+1) poly(k, log(q+m+2)), where m is the number of sparse labeled monomial records. Recovering the exact address image by quadratic Walsh sums costs an additional 2^k poly(k). Consequently the entire variable-incidence quadratic packed SAT promise of the preceding handoff admits deterministic O(n log^C n)-size AIG circuits for some absolute constant C, and hence o(n^1.01) circuits. This supersedes the randomized-only upper bound for this promise, but does not improve the unrestricted SAT gate-count lower bound. No claim of literature priority or practical circuit synthesis.

All polynomials below are Boolean multilinear over GF(2). Polar forms are alternating bilinear. A monomial record consists of at most two variable indices and a k-bit vector coefficient; duplicate records add by XOR, a repeated index is linear, and zero coefficients may be omitted. Constants are allowed. The natural packed length is n=Theta(M), M=2^k, with q<=m=Theta(M/k) (use the entire nonzero label pool, including unused variables, for fixed circuit dimensions). Any padding length at least the natural length can ignore its fixed suffix. For the balanced promise, read the original prefix. No monotone size claim is needed for the unrestricted target.

## 1. High-rank marginal lemma: exact support rather than exact histogram

Write B(x,y)=F(x+y)+F(x)+F(y)+F(0), the vector-valued polar form. For lambda in GF(2)^k, let B_lambda=lambda dot B. Let Lambda be any linear subspace of the dual output space of dimension t, with a basis defining a projection pi: GF(2)^k -> GF(2)^t.

**Lemma.** If rank(B_lambda)>=4k for every lambda outside Lambda, then

    im(F) = pi^(-1)(im(pi F)).

The forward inclusion is trivial. For the reverse, define beta_lambda=E_x (-1)^(lambda dot F(x)). The quadratic character identity (proved in coupled_existential_handoff.md and quadratic_compression_handoff.md) gives |beta_lambda| either zero or 2^(-rank(B_lambda)/2). Fourier inversion gives

    2^k Pr[F(x)=a]
      = sum_(lambda in Lambda) (-1)^(lambda dot a) beta_lambda
        + sum_(lambda outside Lambda) (-1)^(lambda dot a) beta_lambda.

The first sum equals 2^t Pr[pi F(x)=pi a] by character orthogonality. If the marginal address is attained, its indicator is a nonzero polynomial of degree <=2t, so its density is at least 2^(-2t) by the elementary minimum-weight lemma in the preceding handoff. Thus the first sum is >=2^(-t)>=2^(-k). The absolute value of the remaining sum is at most (2^k-2^t)2^(-2k)<2^(-k). The full count is strictly positive. The t=k case has no remaining sum; the t=0 case has first sum one. This lemma deliberately preserves support, not probabilities. A lower-rank cutoff can use rank>=2(k+t); 4k is a uniform convenient choice.

## 2. Orthogonal blocks: simultaneously certify high rank

For W a list of vectors, define the common polar orthogonal complement

    V(W) = {v : B(w,v)=0 for every w in W}.

This is the kernel of a matrix L containing at most k |W| scalar constraints. Start with W empty. Repeat for 2k rounds:

1. Compute U=span{B(x,y) : x,y in V(W)} in GF(2)^k.
2. Choose a basis of U consisting of actual values B(x_i,y_i), with x_i,y_i in V(W), at most k pairs.
3. Append the pair vectors to W as one block. If U=0, stop (the residual will not change).

Finally let V=V(W), U_final=span B(V,V), and Lambda=U_final^perp. There are at most 4k^2 vectors in W and at most 4k^3 constraints in L. Distinct blocks are orthogonal for every component of B because later vectors were selected from the common orthogonal complement of all preceding vectors.

For any lambda outside Lambda, B_lambda is nonzero on V. V is contained in every earlier residual. Each round's selected labels span the earlier residual's labels, so in each block some pair satisfies B_lambda(x_i,y_i)=1. Those 2k selected pairs are mutually orthogonal across blocks and individually nonsingular for B_lambda (alternating two-dimensional block). Their direct sum is nonsingular: testing a putative dependence against each partner forces all its coefficients to vanish. Therefore rank(B_lambda restricted to span W)>=4k. If the procedure stopped early, U_final=0 and Lambda is the whole dual space, so no high-rank condition is required. The original map also has rank>=4k for every outside combination.

This is the key change from the previous fixed-sketch strategy. W is chosen adaptively from the actual coefficient list, not from a universal collection of candidate affine maps.

## 3. Preserve the low-rank marginal exactly with a small subspace

Let r=rank L<=4k^3. Choose pivot coordinates I of size r such that L restricted to their span S has rank r. Then GF(2)^q=S direct-sum V. For lambda in Lambda, B_lambda vanishes identically on V x V. Consequently pi(F(v)+F(0)) is linear in v on V. Define the linear signature on V

    sig(v) = ( pi(F(v)+F(0)), (pi B(s_i,v))_(i in I) ),

where s_i is the standard basis vector of pivot coordinate i. This has t(1+r)<=k(1+4k^3) bits. Choose Z consisting of vectors of V whose signatures form a basis of the signature image; at most t(1+r) vectors suffice.

For any x=s+v, choose z in span Z with sig(z)=sig(v). Then

    pi F(s+z) = pi F(s) + pi(F(z)+F(0)) + pi B(s,z)
              = pi F(s+v).

Thus E=span(W union {s_i} union Z) preserves the entire marginal image. Its dimension is at most

    4k^2 + 4k^3 + k(1+4k^3) = O(k^4).

It contains W, so the high-rank bound for every lambda outside Lambda holds also on E. Apply Section 1 both to F and F restricted to E: their marginal images coincide, hence their full images coincide. The conclusion concerns existence of an exact image-preserving linear compression, not equality of full histograms. If using a dependent generating list instead of an independent basis for E, pulling the form back by the surjection onto E preserves the rank (the kernel simply supplies radical directions), and the image is unchanged.

## 4. Construct U without enumerating all 2^k combinations

A rank-threshold oracle and an elementary augmented-matrix identity make the orthogonal blocks constructive with only poly(k) calls on sparse data.

Given V=ker L and r=rank L, for any lambda define the scalar alternating matrix A_lambda of B_lambda and the augmented matrix

    K_lambda = [ A_lambda   L^T ]
               [ L          0  ].

Then

    rank K_lambda = 2r + rank(B_lambda restricted to V).

Proof: discard redundant constraint rows by invertible row operations and the corresponding column operations (the discarded directions are zero). Choose domain coordinates S,V such that L is [I_r 0]. In order S,V,constraint the matrix is [A C I; C^T D 0; I 0 0]. Pair the S and constraint blocks, which together are nonsingular of rank 2r. Eliminating the C coupling by adding appropriate constraint directions to V leaves the V block D unchanged, since constraint directions have zero pairing with V and with each other. This proves the identity, including r=0 and V=0.

It suffices to determine whether rank K_lambda>2r. Suppose a rank oracle supplies row and column indices of a nonsingular minor of order >2r. Let H be the union of its row and column indices that are original variable coordinates, together with the r pivot coordinates of L. Restrict the original variables to span of coordinates H, keeping all constraint coordinates. The minor is retained and L_H still has rank r. The augmented identity shows B_lambda is nonzero on ker(L_H). Construct a basis of this small kernel and test pairs, finding x,y with lambda dot B(x,y)=1. If the rank oracle returns a minor of order <=2r and its reported rank is exact or truncated at a threshold strictly greater than 2r, B_lambda is zero on V.

To find U, start with an empty basis of labels. For a basis of its annihilator, test each lambda by the augmented-rank oracle. If any test finds a nonzero pair, its vector label lies outside the current span, so append it. If all basis tests are zero, linearity shows every label in B(V,V) lies in the current span (the double annihilator). At most k successful iterations and O(k^2) tests per block. The 2k rounds plus the final span computation use O(k^3) tests. Each augmented rank threshold can be fixed at 2D+1 with D=4k^3, irrespective of the actual rank r<=D; compare returned truncated rank with 2r. A certificate contains O(k^3) row/column indices; hence all kernel and pair work on H is polynomial in k. Constraints may be padded with zero rows and loops may be padded with no-ops.

## 5. Sparse rank-threshold certificates in quasi-linear Boolean circuit size

The gate bound here is important. A dense q by q elimination, or evaluating all 2^k forms on the original q variables, would not suffice. We give a self-contained sparse-record implementation. It is a paper circuit construction, not what the Python bit-vector runtime measures.

**Sparse certificate lemma.** For an a by b binary matrix specified by S sparse entry records (indices, coefficient bits, active flag; duplicates XOR), and threshold T>=1, a deterministic fan-in-two Boolean circuit of size (a+b+S) poly(T, log(a+b+S+2)) returns min(T,rank A) and equally many original row and column indices of a nonsingular minor. The matrix dimensions and record budget are fixed per circuit. All numbers of gates below are bounded by a fixed polynomial in T and index widths times the record budget.

Use a balanced binary tree of row-index intervals, padding the number of rows to a power of two. At each node retain at most T independent *original* rows. When the true rank of that row block is <T, retain a full row basis; otherwise retain any T independent rows. To merge two children, examine the matrix of their <=2T retained rows, with original columns. Take up to T independent columns; then choose independent rows on those columns. The selected square minor is nonsingular. If either child was truncated, the candidate matrix already has rank >=T; if neither was truncated, the candidates span all original rows in the parent block. This proves by induction that the truncated rank at the root is correct, and all retained entries remain original rows, never dense elimination rows.

Implementation at each level uses a fixed array of O(a+b+S) records, sorted and scanned, not a q^2 array:
- Initially XOR duplicates by sorting on (row,column), marking zero/dummy records inactive. A leaf row has slot 0. At a merge, each retained entry carries its original row and column, its child-group ID, and its row's slot <T. The parent group's candidate slot is determined from child side and old slot, in [0,2T). Parent group is the fixed binary interval containing the row.
- Sort active entry records by (parent group,column,candidate slot). A scan combines each group's equal-column records into a <=2T-bit column vector (XOR contributions; zero vectors do not add rank). A second segmented scan runs ordinary Gaussian elimination on these small vectors, with a basis capped at T. Retain the original independent column vectors and their column IDs along with residual pivots; also record original row IDs for candidate slots that occur. For each group, reset state at its boundary. All scan states and per-record updates have poly(T,log(a+b+S+2)) bits/gates. A scan is unrolled as one step per record slot, with conditional updates and inactive dummy slots; it need not be parallel.
- At a group's last record, compute by small Gaussian elimination which candidate rows form an independent basis on the retained columns. Emit a summary record with selected row slots, new slot numbers, and (if needed) minor IDs. Allocate a potential summary at each array slot with an active bit, so the number of slots never depends on input. Sort summaries and original entries together by group, summary before entries, and scan to copy the group's selection to each entry. Inactivate entries from discarded rows, and assign retained rows their new slots. The active entry records for the next level are a subset of the preceding original entries. Empty groups need no active records and contribute zero rank.
- At root read the retained row and column IDs. If there are no active entries return rank zero. Arrays of variable logical size are fixed-capacity arrays with flags. All indexing into poly(T)-size arrays can use ordinary multiplexers. Sorting records can use a Batcher network with O(N log^2 N) comparators on O(poly(T,log N))-bit keys and payloads, each comparator implemented with O(poly(T,log N)) binary gates. There are O(log(a+1)) levels; summary record slots are reused each level, not accumulated.

This proves the stated Boolean circuit bound for the oracle. There is no RAM-only assumption about random access or dynamically growing row lengths. The independent-row reference in deterministic_quadratic_check.py exercises the same algebraic merging rule but uses Python integers and dictionaries, not synthesized sorting networks.

## 6. Implementing the complete compressor at quasi-linear cost

Let the sparse map have m monomial records, with k-bit coefficients and variable indices in [q]. Use a fixed record list and padding flags; it can be extracted from the packed promise by decoding row index of each logical slot, witness labels, pattern parity, and table bits as in the previous handoff. Duplicate monomials may be retained as XOR sums or aggregated by sorting their ordered endpoints. All needed sorting joins can use the same table-before-query record technique as the earlier randomized circuit.

- Maintain at most 4k^2 selected vectors W as a q by O(k^2) bit table. To form L, each cross monomial c e_i e_j adds the coefficient bits times w_i to the constraint column j and times w_j to column i. Retrieve the required W entries using sorting joins by endpoint, then aggregate by column using segmented XOR. This requires (q+m) poly(k, log(q+m+2)) gates. Linear and constant terms contribute nothing to B. Form the augmented matrix as scalar sparse records from A_lambda (at most 2m records) plus O(q k^3) entries from L and its transpose. The sparse certificate lemma applies with T=O(k^3). Redundant and zero rows cause no problem.
- Compute pivot columns I of L by scanning its q columns of length <=4k^3 and retaining a small independent basis. All pivot bookkeeping is polynomial in k per column. For the restricted witness extraction on H, compare each sparse monomial's endpoints with the O(k^3) chosen indices, aggregate small dense matrices and use ordinary small Gaussian elimination. The label B(x,y) is evaluated from the sparse records or the small matrices. This costs (q+m) poly(k,log(q+m+2)) per test. Number of tests is O(k^3), so the overall exponent in the polynomial factor is absolute.
- For the signature step, do NOT materialize q dense vectors of length q. For each nonpivot coordinate j, solve for its L-column as a linear combination of pivot columns, obtaining a vector C_j supported on I; f_j=e_j+C_j is a kernel basis vector. Each such vector is represented by j plus <=r coefficient bits. This uses poly(k) gates per column. Compute the signature of all f_j using the quadratic identities G(x)=F(x)+F(0), G(e_j+C_j)=G(e_j)+G(C_j)+B(e_j,C_j), and B(s_i,f_j)=B(s_i,e_j)+B(s_i,C_j). The necessary data are the linear coefficient at each j, the small polynomial on pivot coordinates, and the polar coefficients B(e_j,s_i) for every j and pivot i. Obtain them from the sparse monomial records by comparing pivot indices, sorting by j and pivot slot, and segmented XOR, with a dense q by poly(k) array (including zero defaults). All evaluations of C_j use only the small pivot table. Scan signature vectors of length <=k(1+4k^3), retain a basis with original f_j tags. Generate E's O(k^4) vectors from W, I and selected f_j (independence optional). This avoids a hidden q^2-size kernel matrix. The total again is (q+m) poly(k,log(q+m+2)).
- Produce compressed quadratic coefficients by substituting the E-generators' coordinate forms in each monomial (sorting joins to look up the forms, multiplication of two linear forms by their explicit O(d^2) Boolean coefficient formula with d=O(k^4), and XOR accumulation). Then apply Section 2 of quadratic_compression_handoff.md: for every lambda, form its scalar polynomial, compute its exact character sum by quadratic pair elimination in O(k d^2+d^3) gates, perform a length-M Walsh transform using signed O(d+k)-bit arithmetic, and check if any address with a nonzero count is marked in the table. Total 2^k poly(k) gates after compression. The count is over compressed coordinates, which may differ drastically from original witness counts; only positivity matters.

All the record routing, scanning and elimination above is on fixed-width arrays with padded control. Any arbitrary lookup in a poly(k)-size state can be implemented using a polynomial-size mux; large q-indexed lookups are batched via sorting joins, not q-way muxes at every query. Bounds are for ordinary nonuniform Boolean circuits, not merely algorithms with a RAM cost estimate. We do not optimize the large absolute polylogarithmic exponent. It is crucial only that it is independent of n. The signed AIG gate basis simulates the Boolean gates with constant overhead.

At the packed scale q,m=O(n), k=Theta(log n), M=Theta(n), so C_det(n)=O(n log^C n) for an absolute C. This is o(n^(1+epsilon)) for every fixed epsilon>0, including 0.01. At small sizes it may be much more expensive than the previous randomized algorithm. No numerical crossover or practically efficient solver is asserted. The earlier fixed-sketch obstruction remains correct for oblivious fixed lists; this construction chooses its subspace from the instance.

## 7. Executed finite verification

Run from this directory: python -B deterministic_quadratic_check.py (imports the previously committed quadratic and permutable checkers). Seed 870010. Actual output: deterministic_quadratic_replay.txt. Source 6802 bytes, FNV-1a ef09e977, SHA-256 4de9f02e4c99df538f86d6dec1e6dd0b12522dbb8cb44a6a94b8294737f1081d. Replay 210 bytes, FNV-1a 84932d39, SHA-256 351b82d3d2fd257e4a631d04ac0f73b8ee1994bb263d9f445cb925ae6012847e.

- 1000 sparse matrix rank-certificate tests comparing truncated rank and nonsingular minor against direct Gaussian rank.
- 232 vector-valued quadratic maps (180 random small, four mixed high/low-rank planted star-plus-pair systems, 48 generated from the exact packed quadratic SAT construction).
- 228 original histograms independently compared against exhaustive enumeration. All 232 compressed supports compared against exact original Walsh histograms (3300 address flags).
- 57 compressed high-rank combination checks, 128 maps with strict dimension reduction, four with nontrivial proper Lambda. Largest tested original variable count 180, largest compressed dimension 83, largest observed dimension reduction 97.
- All assertions passed on two local executions. This tests the rank algebra and compression on modest systems, not the actual sparse Boolean routing circuits or asymptotic runtime. The rank certificate reference works on integer row masks; it is not an implementation of the sorting-network circuit. The packed test imports the previous grammar and polynomial reference rather than repeating its pinned SAT tests.

No Lean executable was available; no new kernel-checked theorem. This is a paper proof plus finite testing. Related standard tools include orthogonal decompositions of alternating forms, Fourier inversion, and sparse elimination. The combined deterministic compression/circuit construction needs independent audit; no novelty claim is made.

## 8. Native-agent priorities and next research target

1. Independently audit Sections 1-3 (the exact marginal support lemma, 2k orthogonal rounds, low-signature preservation); these have standalone algebraic statements suitable for Lean. Then audit the augmented-rank identity and witness extraction. Do not add unproved axioms to label results verified.
2. Replay the committed script. Independently verify the sparse rank merge circuit and the batched signature computation, including fixed record capacities, padded controls and handling of empty groups. If desired, implement an actual bitonic sorting/scan circuit on tiny matrices as a regression. Do not confuse Python integer timing with gate count. This is the central cost argument to review.
3. The deterministic O(n polylog n) upper bound, if independently confirmed, rules out the *whole* quadratic packed witness promise as a standalone source of a deterministic n^1.01 lower bound. It does not rule out using it as one of many restrictions of full SAT. The near-cubic formula bound and delta-free sharing theorem remain valid; no new unrestricted gate-count lower bound has been proved.
4. Move to genuinely higher-degree coupling or to simultaneous heterogeneous SAT restrictions. Degree-three witness products retain the exact grammar, bounded copying and fiber-density lower bound 2^(-3k), but neither the quadratic polar rank criterion nor the pair-elimination Walsh routine generalizes directly. Identify a semantic invariant whose cost is charged to distinct gates; merely increasing witness degree, witness multiplicity, or path multiplicity does not prove hardness.
5. Keep all current work in chatgpt_handoff. Reuse the native agent's earlier checked LookupProjection, ParityLookup and CircuitLemmas.Unfold modules rather than repeating uncompressed Andreev work. Tal's revised formula composition theorem remains an external mathematical premise. PackedAndreevLemmas.lean is an unverified draft. No native solver or verified Lean library modifications were made.

L-clb-036 remains open.
