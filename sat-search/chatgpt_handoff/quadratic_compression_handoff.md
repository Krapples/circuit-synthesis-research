# Quadratic existential witnesses: exact Walsh image and randomized compression

Date: 2026-11-26. Base handoff: 575f7bebfa11d3e8d6052dfc386ca66f91c687fe. Read [coupled_existential_handoff.md](coupled_existential_handoff.md) and [permutable_andreev_handoff.md](permutable_andreev_handoff.md) first. This round executes the previously paper-only quadratic projection and rank criterion, and proves a randomized quasi-linear promise-circuit upper bound plus a limitation of oblivious derandomization. No unrestricted SAT gate-count lower bound, no Lean verification, and no novelty claim relative to the literature. L-clb-036 remains open.

## 1. Exact paired-grammar quadratic projection

Use the earlier parameters M=2^k, ell=Theta(k), J=floor(M/(k ell)), r=J ell, m=kJ=Theta(M/k), P=2^ell, B=M/ell, A=k(2J-1)+2B-1. Physical slot i contains ell source bits, a permutation-selected logical slot pi(i), and two programmable witness labels u_i,v_i in {0,...,m}. Let e_0=0, with other used witness bits free.

Use the previous U and V dictionaries, row XOR chains and data guard tree. Reserve A+3m+1 auxiliary identifiers of common width in [Q',2Q'-1], where Q' is the least power of two >=max(4P,A+3m+1). Assign consecutive IDs to the old A auxiliaries, then m temporary chunk values t_i, then m temporary products p_i, then m+1 witness variables e_u. In each physical slot replace its two equality clauses by:

- Two clauses fixing t_i to U_(pattern_i).
- Three clauses fixing p_i=e_(u_i) AND e_(v_i).
- Four XOR clauses fixing z_(pi(i))=t_i XOR p_i.

Add the unit fixing e_0 to zero. Duplicate witness labels are permitted, in particular u_i=v_i gives a linear term and either label zero gives a zero term. All these clause slots have fixed arity, and all auxiliary identifiers have equal width. The only programmable data/selector digits are the same pattern digits regardless of permutation and label assignments; each selector bit has two copies and each data bit one. The physical coordinates are disjoint as before. The encoding is Theta(M) bits: O(m) extra clauses with O(k)-bit identifiers, and the old dictionary and guard costs remain O(M). Apply the earlier exact padding and signed balancing if needed.

For a fixed assignment to all used witness bits, every used auxiliary value is forced until checking the output. If j=pi(i)//J is the logical row, XOR the contribution e_(u_i)e_(v_i) into coordinate j. Let Q(e) be the resulting quadratic map (multilinearized using e_u^2=e_u), and b the selector-row parity offset. The formula is satisfiable iff the accepting data table intersects the image of F(e)=b XOR Q(e).

Setting every witness label to zero recovers the entire permutable packed Andreev restriction, so its formula and distributed high-path theorems persist at this length for deterministic circuits correct on the whole quadratic promise. This does not assert high-path counts for individual seeds of a randomized circuit.

## 2. Exact image via quadratic character sums

For lambda in GF(2)^k define the scalar quadratic polynomial P_lambda(e)=lambda dot F(e), and let

    C(lambda) = sum_e (-1)^P_lambda(e).

The full address histogram is

    N(a) = 2^(-k) sum_lambda (-1)^(lambda dot a) C(lambda).

Thus all counts are recoverable by a single length-M fast Walsh-Hadamard transform. No approximate arithmetic is needed.

To compute C(lambda) for a scalar polynomial in d variables, select any nonzero cross term xy and write

    P(x,y,z) = xy XOR x L(z) XOR y R(z) XOR P0(z),

where L,R are affine and P0 is quadratic. For each z,

    sum_(x,y) (-1)^(xy+xL+yR) = 2 (-1)^(LR).

This follows by summing over y first: only x=R contributes. Replace P by P0 XOR LR, remove x,y and multiply the remaining sum by two. If t pairs were removed, the remaining polynomial is affine on d-2t variables: a nonconstant affine polynomial has character sum zero, otherwise the original sum is +/-2^(d-t) according to the remaining constant. All arithmetic on polynomial coefficients is in GF(2). This algorithm also works for d=0 and constant maps.

For a dense coefficient representation, pair elimination can be unrolled into O(d^3) binary gates, including input-dependent pivot choice. At each of floor(d/2) stages, form a one-hot selector for the first nonzero off-diagonal coefficient by a prefix scan over O(d^2) coefficients. Derive one-hot row and column selectors; read their linear and quadratic coefficients via Boolean multiplexing in O(d^2) gates. Mask out both selected variables from L,R and from the old coefficients. Compute all coefficients of LR in O(d^2) gates (constant L0R0, linear L0Ri+LiR0+LiRi, cross LiRj+LjRi), XOR into the residual, and update the pair count. When no pivot exists, leave the polynomial unchanged. Removed variables never reappear; the unused positions can remain zero in a fixed-size array. Count t in O(log d) bits; encode the final signed power of two or zero in O(d^2) gates. The total bound is O(d^3) including control, not a RAM-only cost claim.

Combine the k compressed coordinate polynomials for each of the M lambdas using O(k d^2) gates per lambda. The transform takes O(M k) additions/subtractions on signed O(d+k)-bit integers; the division by 2^k is exact. Accept iff some a has N(a)>0 and h[a]=1. This gives exact image for any supplied quadratic system; without compression the d=q gate bound is not quasi-linear.

The earlier rank criterion is recovered directly: eliminating a cross term splits off one nonsingular alternating two-dimensional block, so t=rank(B_lambda)/2 (equivalently use the radical proof in the preceding handoff). Hence C(lambda) is zero or has magnitude 2^(q-rank/2). If all nonzero combinations have rank >=2k, Fourier inversion gives N(a)>0 for every a. An omitted address requires some nonzero lambda of nonzero bias and rank <=2k-2. The checker independently computes polar ranks, pair sums and exhaustive address counts.

## 3. Small affine compression: image preservation

Lemma (elementary minimum-weight Reed-Muller bound): a nonzero Boolean multilinear polynomial of degree at most D has support density at least 2^(-D). For a proof choose a monomial of largest degree t<=D with nonzero coefficient. Fix all variables outside that monomial arbitrarily. Its coefficient is still one, since any other monomial that could contribute to this coefficient would strictly contain it. The restriction is a nonzero function on t bits by uniqueness of multilinear representation; it therefore takes value one at least once. Averaging over outside assignments gives density >=2^(-t)>=2^(-D). This is a standard coding-theoretic fact; see e.g. https://doc.sagemath.org/html/en/reference/coding/sage/coding/reed_muller_code.html (minimum distance). The argument here is self-contained.

For any address a, its fiber indicator is the Boolean polynomial

    I_a(e) = product_(j=1..k) (1 XOR F_j(e) XOR a_j).

Its degree is <=2k after multilinearization. Thus if a is attainable, its fiber density p_a is >=2^(-2k). The exponent is sharp for k independent ANDs with target all ones (exactly one assignment out of 2^(2k)). Also, a nonzero polynomial of degree <=2k has an accepting input of Hamming weight <=2k: choose an inclusion-minimal monomial of nonzero coefficient and set exactly its variables to one. Consequently every attainable address has some witness of weight <=2k relative to the all-zero baseline. This is a witness existence lemma, not an efficient search over all subsets.

Choose a uniformly random affine map T(z)=c+Lz from GF(2)^d to GF(2)^q (independent unbiased entries of c,L). It need not be injective. For distinct z,z', the pair (T(z),T(z')) consists of independent uniform points of GF(2)^q: each output row gives two independent linear forms in its random coefficients, because the vectors (1,z) and (1,z') are linearly independent over GF(2). Thus the 2^d evaluations of a fiber indicator are pairwise independent.

Let X count points z with F(T(z))=a. E[X]=2^d p_a and Var[X]=2^d p_a(1-p_a). Chebyshev gives

    Pr[X=0] <= (1-p_a)/(2^d p_a) <= 2^(2k-d).

The compressed image is always a subset of the original. For d=3k+2, union bound over <=2^k attainable addresses gives probability of any omitted address <=1/4. In particular, a dimension-at-most-(3k+2) affine subspace preserving the entire image always exists, even if q is enormous. For the SAT decision alone, use d=2k+2: whenever the original accepts, fix any attainable accepting address and bound its omission by <=1/4. The algorithm never falsely accepts a negative input. For fixed q<d, the same affine sampling proof works without a rank assumption on L; alternatively use the identity map.

This is an RP-style, one-sided randomized reduction to O(k) witness dimensions. It does not enumerate the 2^d restricted points. Instead use Section 2 to compute all M address counts exactly in the compressed polynomial system.

## 4. Randomized quasi-linear promise-circuit upper bound

Let n be the paired word length (Theta(M) for the constructed family at a fixed scale, and >= that length after allowed padding). Here k=Theta(log n) when the scale is chosen by the earlier bounded-ratio padding rule, m=O(M/k), and a witness label is O(k) bits. The entire promise allows the permutation, witness labels, pattern bits and table bits to vary. Use one random affine form in d=2k+2 (or 3k+2 for image preservation) for each of the m nonzero label IDs, and form zero for label 0. This requires O(md)=O(M) random bits. The following is an explicit bounded-fanin randomized Boolean circuit construction:

1. Extract fixed positions for logical slot indices, witness labels and pattern parities. Route each of the 2m witness-label queries to its affine form using sorting networks on O(m) records, including one table record per label, sorted by (label, table-before-query). Scan to copy the current label's form into all its queries. Sort back by physical slot and operand index. Records have O(k) bits, so O(m log^2 m) compare-exchanges of O(k) gates each cost O(M k^2); the scans cost O(mk). This avoids an expensive independent random-access mux per query. Table record for zero has constant zero form.
2. Compute the product of two affine forms in O(d^2) gates per slot by the explicit Boolean coefficient formulas above. Add its pattern parity to the constant coefficient. Compute a one-hot logical row index by comparison with the k known row intervals (O(k^2) gates per slot suffices). Mask each coefficient by this row selector and XOR across all slots. This produces all k compressed quadratic coordinate polynomials in O(m k d^2)=O(M k^2) gates. The product expansion also handles repeated labels and label zero.
3. Compute each of the M scalar quadratic character sums in O(kd^2+d^3)=O(k^3) gates as in Section 2. Total O(M k^3). Run one Walsh-Hadamard transform in O(M k(d+k))=O(M k^2) gates. Compare counts with zero and combine with the data table in O(M) gates.

Signed AIG simulation adds only a constant factor. The resulting randomized circuit uses O(n log^3 n) binary gates and O(n) random bits, has false-positive probability zero on the promise, and false-negative probability at most 1/4 on each promised positive word. The same algorithm works for the balanced promise by reading the original prefix; no monotone randomized compilation is claimed here. This is an analytical circuit-size bound, not a synthesized gate count or a deterministic circuit bound. In particular, it rules out proving a randomized superlinear exponent lower bound merely on the quadratic promise, but does NOT rule out a deterministic lower bound for it.

For fixed incidence (fixed permutation and witness labels), the image of Q is fixed independently of selector patterns and h. Choose once a good affine map preserving that image and hardwire it, so the same bound becomes deterministic. In fact an O(M k^2) deterministic bound follows by hardwiring the indicator of im(Q): use XOR convolution of this indicator and h, by integer Walsh transforms and pointwise O(k)-bit multiplication, then mux at b and test positivity. Intermediate integers have O(k) bits; the result counts accepting addresses. This fixed-incidence observation applies to any witness-address function with k output bits, regardless of degree. It does not solve varying incidence.

For varying incidence, naive nonuniform error reduction gives deterministic O(n^2 log^3 n): OR O(n) independent fixed-seed circuits after choosing a seed list by a union bound over at most 2^n inputs. It is not an O(n^1.01) deterministic bound. The next section shows why directly fixing only polylogarithmically many affine maps is not enough for this particular algorithm.

## 5. Oblivious sketch-list obstruction (genuinely quadratic)

Consider any fixed list of t affine maps T_l: GF(2)^d -> GF(2)^m into the full nonzero witness label space, independent of the instance. Assume k>=2 and t(d+1)<J. Restrict attention to the first J label coordinates. For each label i in this set, concatenate its affine coefficients under all t maps (constant included), giving a vector v_i of length t(d+1). Since J>t(d+1), the v_i are linearly dependent. A nonzero vector of dependence coefficients alpha gives a nonzero linear form

    L(e)=XOR_(i<=J) alpha_i e_i

which vanishes identically on every T_l. Choose one fresh label w=J+1 (available since m=kJ). The nonzero quadratic polynomial e_w L(e) also vanishes on every sketch.

This is realizable in the actual promise: identity permutation, zero source pattern bits, row zero containing one slot with label pair (w,i) for each alpha_i=1, all unused slots and other rows using (0,0). Choose h[1]=1 and all other data bits zero. The word is satisfiable by setting one alpha_i=1 witness and e_w to one, and other witnesses to zero. Every fixed sketch produces only the all-zero address and falsely rejects. This uses genuine degree-two cross terms, not just a linear special case.

Therefore any input-independent list of affine maps whose restricted-image union decides every such promised input must satisfy

    t(d+1) >= J = Theta(M/k^2).

For d=O(k), t=Omega(M/k^3)=Omega(n/log^3 n) at the natural padded scale. This is an obstruction to the oblivious fixed-sketch OR strategy, NOT a gate lower bound for arbitrary deterministic circuits. It assumes fixed coordinates for the entire witness label pool; input-dependent compression, changes of basis, or arbitrary decision algorithms are not covered. In particular it does not apply to adaptive choices of affine subspaces. This also shows why the successful random compression must not be silently interpreted as a single universal deterministic projection.

## 6. Executed verification and limits

Run from this directory: python -B quadratic_witness_check.py. The script imports the previously committed independent packed grammar reference. Seed 870009. [Actual stdout](quadratic_witness_replay.txt):

- 84 generated quadratic packed instances, k=1..7, with <=4 active nonzero witness labels.
- 1,096 original and 1,096 balanced pinned-witness SAT checks by unit propagation; 28 source-coordinate flip probes under changed permutations and labels.
- 2,964 independent polar-rank versus exact-character checks; 180 exact histogram comparisons with exhaustive enumeration; 76 missing-address cases satisfying the rank criterion.
- 4,880 compressed polynomial evaluation checks. Full image preserved in all 84 sampled d=3k+2 compressed instances (small q; not a large-dimensional success benchmark).
- 256 deliberately rare-fiber sketches for independent ANDs (density 2^(-2k)); 22 misses at d=2k+2. These are expected false negatives, not failed assertions; randomness is not assumed to preserve image deterministically.
- 26 high-rank combination checks on planted surjective quadratic maps.
- 128 constructed annihilator/product counterexamples to fixed short sketch lists in the abstract quadratic polynomial model.
- All executed assertions passed. Source length 8260 ASCII bytes, FNV-1a 32-bit 4775149e. Replay length 357 ASCII bytes, FNV-1a 86d49203.

The circuit construction is a paper argument. The Python coefficient operations are not synthesized AIG gates and their runtime is not the claimed circuit complexity. The fixed-list test checks the abstract counterexample polynomial, not an exhaustive adversarial SAT circuit search. No Lean executable is available in this environment; no new kernel-checked claim. Related standard tools include Reed-Muller minimum distance, quadratic Walsh sums, and sorting networks. No claim of priority for these tools or their combination.

## 7. Native-agent priorities

- Replay the three current scripts and formalize quadratic gadget semantics, exact paired-coordinate multiplicity and the pair-elimination character-sum identity. Reuse SatBridge.LookupProjection, SatBridge.ParityLookup and CircuitLemmas.Unfold where appropriate. Keep Tal's composition theorem as an explicit external mathematical premise.
- Independently audit the randomized circuit routing and pivot cost, and the fixed-list annihilator proof with its precise quantifiers. Do not infer deterministic quasi-linear SAT circuits or a deterministic lower bound from randomized results.
- Investigate input-dependent deterministic compression for sparse quadratic witness systems, or a genuine deterministic gate-count argument for the varying-incidence quadratic promise. The fixed-incidence upper bound rules out a single frozen template from this family as a witness for L-clb-036.
- If pursuing more expressive nonlinear systems, note that the density/compression lemma extends to degree D with dimension Dk+O(1) for decision and (D+1)k+O(1) for the whole image, but the efficient quadratic character-sum algorithm does not automatically generalize to degree >=3. This is a concrete point where the current quasi-linear randomized construction may stop working; do not assume higher degree alone implies hardness.

No native solver or verified Lean library changes proposed. L-clb-036 remains open.
