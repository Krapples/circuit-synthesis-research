# Parallel affine-fiber elimination and coupled slope/ingress bounds

Date 2026-11-26. Starting head observed 48edcd4be9b33c944a56cde6308df000f7aca4c9. Extends [affine-prefix rank reserve](affine_prefix_rank_reserve_handoff.md), [symplectic rank profiles](symplectic_rank_profile_handoff.md), [packed directional lookup](packed_directional_handoff.md), and [shared-witness restriction](response_period_handoff.md). Paper proof and exact regression; no independent audit, Lean verification or originality claim. L-clb-036 remains open. No production modifications.

## 1. Setting and target invariants

Contract XOR/NOT wiring in an XOR-AND circuit with free affine operations. Split primaries into d data bits x and query bits q, with a common allowed query domain Y independent of x. All data assignments allowed for each query. Every original AND has operands
    u_i = a_i.x + p_i(q) + alpha_i.g_<i,
    v_i = b_i.x + r_i(q) + beta_i.g_<i,
where a_i,b_i are raw data linear coefficient vectors, p_i,r_i affine in query, constants included. Outputs F_j are affine combinations of primaries and gate outputs. Let t_D count the syntactically data-dependent ANDs, i.e. any AND with a data primary in its contracted transitive ancestry. It includes both pure data and mixed ANDs in the earlier partition. Syntactically query-only gates cannot have nonzero raw data forms or data-dependent predecessors. No claim about semantic mixed gate count.

For each output j collect those q in Y for which the full residual F_j(x,q) is affine as a function of x, and write its linear coefficient as s_j(q). Choose any one reference among the affine contexts for that output, if nonempty. Define D to be the span of all within-output slope differences s_j(q)+s_j(q_ref); equivalently all pairwise differences for each j, with span taken jointly across j. Empty or singleton context sets contribute zero. Do NOT compare slopes of different output coordinates without subtracting each output's own reference. Let rho=dim D.

Define E={a : for each output j, D_a F_j(x,q) is constant in x AND q}. The constant may differ between outputs, but for each output must be common across all data and query assignments. E is a linear subspace by the derivative cocycle. Let eta=d-dim E. Every a in E annihilates all within-output affine slope differences, so D subset E^perp and rho<=eta. This E differs from the exact period space (allows constant nonzero derivatives) and from separate per-context affine directions (requires the same derivative constant for all q).

Let L_raw=span of all a_i,b_i and ell=dim L_raw. If a annihilates all raw data forms, every gate output is invariant under translation by a, inductively. The direct affine primary contribution to each output changes by a constant common to all queries. Thus L_raw^perp subset E, so eta<=ell<=2t_D. These are bounds on the contracted circuit; no assumption that actual input relevance or affine period codimension equals residual entropy.

## 2. Parallel affine-fiber elimination

Maintain a data subspace K=S^perp where S is the span of raw forms selected so far, and an offset c(q) in GF(2)^d for each query. Initially K=full data space, S=0, c=0. Invariant after processing gates 1..i: each processed gate is constant as a function of k on x=c(q)+k for k in K, with its value permitted to depend on q. Crucially the SAME K works for every query. Offsets need not be affine in q and are used only in a mathematical restriction, not treated as free gates of the original circuit.

At the next gate, the earlier gate outputs are already independent of k. Therefore each of its two operands on the fiber is affine in k, with slope equal to its raw data form restricted to K.
- If both a_i,b_i vanish on K, the new gate output is already independent of k, and no constraint is added.
- Otherwise choose ANY one of the two raw forms l_i nonzero on K. Choose a direction v in K with l_i(v)=1. Evaluate the chosen operand at the current representative c(q) for each q. If its value is 1, replace c(q) by c(q)+v; otherwise keep it. Then restrict K to K intersect ker(l_i). This is a parallel affine subfiber of the old fiber for every q, making the chosen operand identically zero. Earlier gate values on that fiber remain unchanged, and the new gate output is zero. Add l_i to S. This increases dim S by exactly one.

The selection of which operand and direction v is independent of q; only the representative update depends on q. Query-only gates never require a constraint. Therefore dim S_final<=t_D and K_final has dimension>=d-t_D. All original AND outputs are now query-only on their respective parallel fibers. Each output becomes
    F_j(c(q)+k,q)=C_j(q)+lambda_j(k)
where lambda_j is its raw affine primary slope restricted to K_final, independent of q. For every affine full-data residual, restriction to a translated fiber does not change its slope on K_final. Consequently all affine slope differences annihilate K_final, i.e.
    D subset S_final.
This holds for EVERY allowed greedy operand selection sequence, not merely existence of a convenient transversal.

In particular t_D>=rho. This gives an ordered necessary condition on the raw data forms of a candidate circuit: at each gate pick either form outside the span already selected, if available; skip only if both forms are in that span. EVERY such completed ordered greedy selection must span D. The proof is valid even with arbitrary reconvergent dependencies, query-only preprocessing, and pure data nonlinear gates, because previous gate outputs have been made constant along the fibers. It counts original AND IDs, at most one selected form per gate. It does NOT bound mixed ANDs alone when arbitrary pure data preprocessing is present, and it does not imply arbitrary substitutions preserve an unrelated SAT promise. All data/query assignments are inside the common domain of the restricted target.

## 3. Coupled slope/ingress theorem

Choose a particular greedy run with priority for quotient directions: if either operand raw form is outside D+S, choose one such form. Otherwise choose any raw form outside S if there is one; skip only if both in S. Let e be the number of steps increasing dim((D+S)/D). Since S grows by one whenever a form is chosen, and D subset S_final, we have
    e=dim S_final-rho <= t_D-rho.

Every raw form in every gate belongs to D+S_final except possibly an unselected second form at one of the e quotient-increasing steps. Proof: if neither form is outside D+S at that step both already lie in D+S_final. Otherwise one outside form was selected and belongs to S_final; the other form is the only possible exception. Therefore
    ell <= dim(D+S_final)+e = rho+2e <= 2t_D-rho.
Combining gives
    t_D >= ceil((rho+ell)/2) >= ceil((rho+eta)/2).
This counts distinct gates and combines affine-slope demands with additional ingress directions instead of adding two overlapping lower bounds. Note eta>=rho; the target-only bound dominates both rho and ceil(eta/2), and can strictly improve both. The actual raw rank ell yields a stronger per-candidate certificate.

A refined version records h, the number of quotient-increasing steps where the second form is independent of D+S immediately after the chosen form is added. Only those steps can contribute an exceptional unselected direction; thus ell<=rho+e+h, h<=e. This is a ledger for the actual greedy run, not a universal target-only bound unless h is separately controlled.

Exact-budget rigidity: if t_D=rho, then ell=rho and L_raw=D. Every valid greedy run selects exactly rho independent forms, terminal span exactly D, and no syntactically data-dependent gate can be skipped. In particular every raw ingress form lies in D and every AND output is invariant under translations by D^perp. This is a necessary structural constraint for equality-budget synthesis. More generally, if t_D=rho+s, raw ingress dimension modulo D is at most 2s. These statements follow without any assumption of an output gate being nonlinear.

Specialization for standard arbitrary two-input Boolean gate circuits: every binary Boolean function is affine in the two operands plus possibly their product, so it can be represented with at most one AND and affine operations. Contracted syntactically data-dependent ANDs have distinct original binary gate IDs with data ancestry in the original circuit (contraction may remove paths but cannot create a new original ancestor). Thus the lower bound also bounds the number of original binary gates with data ancestry, although the free-affine AND bound need not be tight for actual binary gate count.

## 4. Direct applications to existing packed SAT restrictions

**Packed INDEX, r=1 in packed_directional_handoff.md.** Data table x of M=2^k bits, query address q; F=x_q. All residuals affine with slopes e_q, so D is the even-parity subspace of dimension M-1. E consists of the two constant directions (zero and all-ones) and eta=M-1. Therefore t_D>=M-1, and a binary mux tree achieves M-1 ANDs using u+q*(u+v) per mux with free affine wiring. This is exact multiplicative complexity, and in a minimum-AND circuit L_raw=D, no query-only AND is available, every AND output is invariant under simultaneous complementation of all table data, and every greedy choice uses one independent data form. The direct raw affine output term must account for the simultaneous-complement flip of the final output. This is stronger structurally than old ingress count ceil((M-1)/2) and aggregate logarithmic rank. It is not an improvement over all known binary-gate multiplexer lower bounds; classical gate elimination and multiplexer complexity have a substantial literature. Background (search only, not full paper audit): NIST Boolean Functions with Multiplicative Complexity 3 and 4, https://csrc.nist.gov/pubs/journal/2020/07/boolean-functions-with-multiplicative-complexity-3/final ; A Survey on The Multiplexer (MUX), https://nathandang97.github.io/documents/manuscripts/MUX_survey_preprint.pdf . No originality claim.

The earlier packed SAT grammar with r=1, M=2^k has single-copy physical table bits and independent address polarity bits. Fixed other physical coordinates yields exactly this target. Thus any SAT circuit on those lengths has at least M-1 original binary gates with ancestry in the designated free table positions (after fixing the other physical constants, or in the original circuit since restriction cannot add ancestry). This is linear in the packed word length. No new grammar or padding replay, no stronger SAT-wide numerical bound claimed.

**Packed shared witness.** F(H,S,Q)=OR_(j in Q) AND_(i in S) H_ij on d=m*ell independent table bits. Empty Q gives the zero residual, and singleton S={i},Q={j} gives individual bit H_ij. Hence D=the full data dual and rho=eta=d. Therefore
    # syntactically data-dependent ANDs >= m*ell.
In the old a,b,t split (a pure data, b pure query, t mixed) this is a+t>=m*ell. In the earlier actual physical packing, ell a power of two with ell=Theta(log m)<=0.5 log2 m, the table data bits occur once each, and independent row-selection and witness-mask coordinates are fixed-position free query bits. All residual contexts used here belong to that grammar; no new grammar replay was performed. The conclusion applies at valid encoded lengths, not arbitrary assumed parameter pairs. This improves the earlier data-direction ingress allocation a+t>=ceil(m*ell/2) from the rank of raw data ingress, and yields t>=m*ell if there are NO syntactically pure data ANDs. It does not prove a mixed-gate-only lower bound with arbitrary pure data preprocessing. The full joint degree m*ell+m+ell already yields stronger total AND count m*ell+m+ell-1; the new result is about which gates must have data ancestry, not a new total SAT size bound. Cannot add separate data and query ancestry counts because mixed gates are shared.

## 5. Exact hybrid family illustrating strict coupled improvement

Let M=2^k, k>=1, r>=1. Data comprise M independent table bits x, plus 2r+1 bits z0,z1,...,z_(2r). Query comprises k-bit address a and enable bits e,b. Define
    F=e*x_a + b*(z0 + sum_(i=1)^r z_(2i-1)*z_(2i)).
All operations GF(2). The affine data residual contexts are exactly b=0, because r>=1 gives a nonzero quadratic component whenever b=1. Vary e and address to obtain slopes 0,e_1,...,e_M in the table coordinates, so rho=M.

E=0: the query e=b=0 gives zero derivative, hence a globally constant derivative must be zero. Contexts b=0,e=1 force every table component of its direction zero. Context b=1,e=0 forces the paired z components zero because the quadratic polar form is nondegenerate on those 2r variables, and then forces z0 component zero. Thus eta=M+2r+1. The coupled theorem yields
    t_D>=ceil((M+M+2r+1)/2)=M+r+1.
Construction: M-1 ANDs for lookup, one AND to enable it, r pair-product ANDs, one AND to enable the quadratic-plus-linear expression. All are data-dependent, total M+r+1. Hence the exact total multiplicative complexity is M+r+1. This strictly improves both rho=M and ceil(eta/2)=ceil((M+2r+1)/2). For M=16,r=8, old bounds 16 and 17, new exact value 25. This family is an abstract benchmark, not a newly packed SAT restriction. Do not claim its exact ordinary binary gate count.

## 6. Constructive rejection certificate for algorithms

If an actual candidate's greedy terminal span S fails to contain a target affine slope difference delta, choose v in S^perp with delta(v)=1 by linear elimination. The two affine contexts q1,q2 witnessing that difference have unequal target derivatives along v. On the candidate's parallel fibers their derivatives are the same raw output slope. Compute the two representatives c(q1),c(q2) by the preceding gate-by-gate procedure; evaluate candidate and target at the four points (c(q_i),q_i),(c(q_i)+v,q_i). At least one is a counterexample to candidate correctness. This only needs the two contexts, not enumeration of all queries; each representative can be tracked by circuit evaluation per processed gate. Given exact affine-slope witnesses, this is a constructive refuter, and the terminal greedy selection itself is a cheap topology/coefficient certificate. No heuristic equality assumption; if only sampled residuals are believed affine without proof, do not enable the rule. No production implementation or benchmark claimed. Engineering agent may integrate after independent audit.

## 7. Executed regression

Run node parallel_fiber_elimination_check.js. Checker body executed in JavaScript tool runtime, not separately in Node or Lean. Seed 870041. 220 pseudorandom scalar/vector XOR-AND circuits on 1..5 data and 1..3 query bits, 1..6 ANDs, plus 14 explicit lookup, enabled lookup, hybrid and shared-witness controls. Exact full truth tables find affine contexts and common constant-derivative spaces. For each circuit test three ordered greedy runs (first available, last available, quotient priority); update query-specific representatives by actual operand evaluations and compare every retained fiber point to its representative for all processed gate values. Check output common slopes and terminal demand-span containment, quotient bound, and rho/eta/ell/t_D inequalities.
    circuits 234; greedy runs 702; gate steps 2628;
    retained fiber-point checks 103800; final output checks 15898;
    affine residual contexts 1071;
    strict hybrid target-bound improvements over max(rho,ceil(eta/2)): 18;
    strict actual ledger improvements over max(rho,ceil(ell/2)): 21;
    observed active gate count equal to target bound: 48.
Controls: ordinary and enabled lookup M=2,4,8; hybrid M=2,4 and r=1,2; shared-witness (1,2),(2,1),(2,2),(2,3), with all target values independently checked. All assertions passed. Small abstract witness parameters need not meet asymptotic packing assumptions. Checker commit fde0008bb9c8d1e73ea6ee9674a4d57a7346294f.

## 8. Scope and next target

The new theorem is a real improvement in distinct-gate accounting and directly applies to the previously packed SAT coordinate restrictions. But it is a linear bound on data-dependent gates. The existing packed functions have linear-size circuits, and adding multiple data-ancestry bounds for overlapping input sets is invalid. For L-clb-036, seek a structural charging theorem that controls how many independent affine slope obligations can be carried by the same original gates across different cut-local restrictions, or a packed restriction with genuinely harder complexity. Investigate whether priority quotient rigidity constrains the query dependence of near-minimal data-gate circuits enough to force additional original gate resources. Use the mux tree as a tight negative control and the hybrid as an exact positive control. Independently audit and formalize the simple parallel-fiber elimination before production pruning. No upstream submission, new physical grammar, or unrestricted superlinear lower bound. L-clb-036 remains open.
