# Coupled existential packed lookup: affine barrier and quadratic rank criterion

Date: 2026-11-26. Base handoff: 870ffb7. Agent work at 5c75256319fcd4f6877c1385a623877e6b58fe60 was inspected: its results/andreev_projection/README.md covers the **earlier uncompressed** polarity projection and checked Unfold, LookupProjection, and ParityLookup lemmas. Reuse those modules rather than repeat that work. The newer packed and permutable constructions and the present extension are paper arguments, not Lean-checked theorems. L-clb-036 remains open.

## 1. Motivation and exact coupled projection

The permutable packed projection forces linearly many high-path gates with no n^(-delta) penalty. Its auxiliary values are deterministic. Does adding shared, genuinely existential witness choices break the quasi-linear promise-circuit barrier? The following affine family shows that even cross-row coupling and exponentially many witnesses are insufficient by themselves.

Use the parameters in [permutable_andreev_handoff.md](permutable_andreev_handoff.md): M=2^k, ell=Theta(k), J=floor(M/(k ell)), r=J ell, m=kJ=Theta(M/k), P=2^ell, B=M/ell, A=k(2J-1)+2B-1. Physical slot i has ell source bits, a logical slot permutation pi(i), and an arbitrary label u_i in {0,...,m}. The label specifies a shared existential variable e_(u_i). Reserve e_0 and fix it to zero.

Replace each two-clause physical chunk block by the two equality clauses forcing t_i=U_(pattern_i), followed by four standard XOR clauses forcing z_(pi(i))=t_i XOR e_(u_i). Keep the XOR row chains, data dictionary and guard tree. Reserve a pool of A+2m+1 auxiliary identifiers of equal width by taking Q' as the least power of two >=max(4P,A+2m+1), and use consecutive IDs starting at Q'. Old logical auxiliaries are the first A, followed by the m temporary t_i, then the m+1 e labels. All programmable pattern digits are in the same fixed positions for every permutation and every label assignment; each selector bit still has two copies and each data bit one. The extra clauses and their fixed-width literals use O(mk)=O(M) bits; total word length is Theta(M), independent of labels, permutation and data. Existing padding and signed balancing apply. The label digits are constants for each projection, but input to a circuit on the union of all promised words.

For each fixed assignment to the q distinct nonzero labels that occur in the input, every other used variable is forced by the dictionary and circuit gadgets before checking the final guard clauses. In particular, the parity address is

    a = b XOR H e

over GF(2), where b is the vector of row parities of the source chunks, and column H_u is the XOR of standard row-basis vectors for slots carrying label u. Thus the exact SAT predicate on this promise is

    exists a in b+im(H) with h[a]=1.

The number of satisfying valuations on the actually used variables is

    2^(q-rank(H)) * |{a in b+im(H) : h[a]=1}|.

This follows from rank-nullity and unique extension for fixed witnesses. It does not count arbitrary values assigned to variables absent from the word. Choosing q=Theta(m) labels each shared between two different rows (pair slots in distinct rows), with all unused slots assigned label 0, gives rank(H)<=k and hence 2^Omega(M/k) satisfying valuations whenever the instance is satisfiable. A table with a single 1 at b gives exactly one accepted address but still exponentially many witnesses. The free label choices really affect the row parities and can couple multiple rows; they are not merely unrelated tautological variables. All-zero h gives a negative instance. This does not assert NP-hardness of the promise.

## 2. The high-path theorem survives; the circuit-size obstruction survives too

Set every label to 0. This recovers the full permutable Andreev projection at the new fixed length with the same copy bound. Consequently the delta-free high-primary and high-internal path-count theorem holds for circuits that decide only this larger existential promise (with n referring to its word length, after optional padding). This is a restriction argument, not a claim that every fixed nonzero label pattern is hard.

The entire larger promise has a deterministic fan-in-two circuit of size O(M k^2)=O(n log^2 n). Here are explicit resource bounds; no general-purpose SAT oracle is used.

1. Extract each slot's logical index, witness label and ell-bit pattern parity. Compute its row index by comparing the logical index against the k fixed row intervals. A k-bit one-hot row vector costs O(k^2) gates per slot; multiply it by the pattern parity and XOR all these vectors to obtain b. Total O(m k^2).
2. Sort the records by witness label, carrying the row vector as payload. A bitonic sorting network takes O(m log^2 m) compare-exchanges, each of O(k) gates. Total O(m k^3)=O(M k^2). Within equal-label runs, compute segmented prefix XOR of row vectors; output only the aggregate at each run end, and output zero for label 0. A sequential unrolled circuit uses O(mk) gates here. These vectors, including zeros, have span im(H).
3. Insert each vector into a k-position echelon basis. Scan pivots from high to low; if a pivot is present XOR its vector, otherwise store the residual in that pivot and zero the residual. Keep presence bits; conditional vector updates use O(k) gates per pivot, O(k^2) per vector and O(m k^2) overall. This is a fixed unrolled Boolean network, not a runtime-dependent circuit size claim.
4. For each of the M possible addresses a, reduce a XOR b against the resulting basis, test zero and AND with the extracted table bit h[a]. OR the M results. O(M k^2) gates. Signed AIG simulation changes the count by only a constant factor.

All operations read fixed token positions on the promised layout; invalid words need not be recognized by this circuit. Padding may be ignored; for the balanced layer read the original prefix. The construction handles arbitrary label assignments, not just fixed H. Since n log^2 n=o(n^1.01), neither raw high-path counts nor the addition of these coupled existential choices suffices to prove the desired lower bound. This is an analytic circuit upper bound, not a synthesized gate count.

## 3. Next semantic target: quadratic shared witnesses (paper lemma)

Replace the XOR contribution e_(u_i) in each slot by e_(u_i) AND e_(v_i), using one extra AND gadget and the same equal-width identifier allocation with a larger constant number of auxiliaries. Allow u_i=v_i (linear terms) and label 0 (zero). This is again O(M) encoded bits with the same fixed data/selector copy positions. The address map becomes F(e)=b XOR Q(e), where each of its k coordinates is a degree-at-most-two multilinear polynomial over GF(2). SAT iff the image of F meets the table's 1-set. Pinning every label to 0 still supplies the hard Andreev restrictions. The affine elimination algorithm does not automatically extend to this family.

A useful necessary condition for a **missing address** follows from quadratic character sums. For lambda in GF(2)^k, define q_lambda(e)=lambda dot F(e), and polar form B_lambda(x,y)=q_lambda(x+y)+q_lambda(x)+q_lambda(y)+q_lambda(0). Let rho_lambda be the rank of this alternating bilinear form, and beta_lambda=E_e (-1)^q_lambda(e).

Squaring the bias and changing variables y=x+d gives

    beta_lambda^2 = E_d [(-1)^(q_lambda(d)+q_lambda(0)) E_x (-1)^B_lambda(x,d)].

The inner expectation is one precisely when d is in the radical, zero otherwise. On the radical, q_lambda(d)+q_lambda(0) is linear. Its signed sum is zero if nontrivial, otherwise the radical has size 2^(q-rho_lambda). Hence beta_lambda is either zero or has absolute value 2^(-rho_lambda/2). Rank is even for alternating forms over GF(2).

Fourier inversion yields for every address a

    Pr[F(e)=a] = 2^(-k) (1 + sum_(lambda != 0) (-1)^(lambda dot a) beta_lambda).

If sum_(lambda != 0) |beta_lambda|<1, every address is attained. In particular, if every nonzero lambda has polar rank >=2k, then the sum is <=(2^k-1)2^(-k)<1, so F is surjective. Conversely, a missing address requires a nonzero lambda with nonzero bias and rho_lambda<=2k-2 (if all nonzero biases had rank >=2k, surjectivity would follow). Thus any UNSAT instance of the quadratic promise with a nonempty 1-set must have a low-rank, nonzero-bias linear combination of its address polynomials. This is a semantic necessary condition on a coupled witness system, not a lower bound on its deciding circuit.

The proposed next step is to characterize the low-rank combinations jointly and determine whether the sparse per-slot representation admits a quasi-linear image test, or whether a stronger gate-count argument can exploit the non-affine coupling. Do not assume low rank implies hardness. The quadratic encoding and character-sum lemma are paper arguments in this round, not executed or Lean checked. No claim of literature novelty.

## 4. Finite replay

Run from this directory: python -B affine_witness_check.py. It uses the independently replayed permutable checker as a grammar and deterministic gadget reference, then exhausts all active witness assignments for each generated instance. For each assignment it pins the witnesses and checks SAT/UNSAT by unit propagation; the underlying deterministic gadget assertion ensures no unresolved clauses remain. It independently computes the GF(2) span, compares the image and counts with exhaustive witnesses, and checks actual paired-word coordinate mutation under different permutations/labels. Seed 870008, k=1..8, 24 instances per k, at most four active nonzero labels sampled. Actual [output](affine_witness_replay.txt): 192 instances, 2,156 original and 2,156 balanced pinned-witness SAT checks, 12,240 address membership checks, 48 coordinate flip probes, 175 multiple-witness cases and 152 cross-row label cases; all assertions passed. These are finite regressions, not asymptotic proofs or large-witness benchmarks.

## 5. Agent tasks and scope

- Replay the packed/permutable and affine checkers. Audit the exact-width allocation, coordinate preservation, telescoping balance and path-count transfer. Read current SatBridge.LookupProjection, SatBridge.ParityLookup and CircuitLemmas.Unfold before integrating. The previous agent formalized the uncompressed projection, not the latest packed version.
- Compile PackedAndreevLemmas.lean as a **draft** in the pinned Lean environment; repair any elaboration failures before moving it into SatBridge. Its local lemmas are not a complete projection proof. Keep Tal's revised Lemma 7.1 as an explicit mathematical premise; do not introduce an unproved axiom to label a result verified.
- Independently formalize the affine gadget semantic identity, rank-nullity witness count, and (after review) the quadratic bias/low-rank criterion. Verify the promise-circuit upper bound at the paper level.
- Investigate nonlinear coupled witnesses, focusing on a semantic-to-distinct-gate bridge for full SAT. Do not claim the affine or quadratic results establish a superlinear unrestricted lower bound. L-clb-036 remains open.

No native solver changes are proposed. No Lean executable was available in the ChatGPT replay environment. No independent native-agent review of these new files has yet occurred.
