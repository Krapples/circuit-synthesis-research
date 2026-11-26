# Five-gate exact mixed rank and last-gate Schur complement

Continues [exact mixed rank ceilings](exact_mixed_rank_ceiling_handoff.md) and [mixed dependency rank transfers](mixed_dependency_rank_handoff.md). Starting head observed 829394b2a71fab0fca8c1882e3384824cd3d5edb. Paper reduction, complete finite enumeration through five mixed gates, and exact last-gate rank identity with finite regression. Not independently audited or Lean checked. No priority claim. L-clb-036 remains open.

## 1. Dependency subspace symmetry

Use the previous syntactic mixed XOR-AND model and translation lift. All pure-side preprocessing may be arbitrary. Each gate in the generic template is G_i=(z_(2i-1)+alpha.G_<i)(z_(2i)+beta.G_<i), and H=lambda.G. The fresh formal variables are independent, and actual data/query ingress maps are pullbacks of the lifted translation tensor. The mixed rank of the latter upper bounds all such actual circuits; equality of maxima follows by using independent actual data and query coordinates for the generic template.

A stronger symmetry than operand swap: at each gate, only the subspace span(alpha,beta) of the formal preceding-output coefficient space matters for rank. Proof: swapping operands swaps the two fresh coordinates and two coefficient vectors. The identity uv=u(u+v+1) replaces the second coefficient vector beta by alpha+beta while changing its fresh variable to z_(2i-1)+z_(2i)+1. This change on the two fresh coordinates is an invertible affine map. Swap and this operation generate GL(2,GF(2)) on the coefficient pair. Rank-zero pairs are already identical; any rank-one pair can be transformed to (0,v) with v its unique nonzero direction; every rank-two pair can be transformed to any ordered basis of its subspace. The entire gate output remains equal after the indicated change of coordinates. Earlier gate outputs are unchanged because they do not use these fresh coordinates; later outputs and the output mask remain equal under substitution because they use the same earlier output values. The changes for different gates use disjoint pairs of fresh coordinates. No arbitrary nonlinear coordinate change or gate-output basis transformation is used.

For an invertible affine map A(z)=Lz+c, the full translation tensor H(A(u+v)) is obtained from H(u+v) by independent permutations u -> Lu+c, v -> Lv. Mixed rank is invariant as well, since it is rank on function spaces modulo constants (or since changing anchors preserves mixed rank). Consequently the canonical subspace representatives cover every rank of ordered templates.

With i preceding gates, the number of subspaces of dimension at most two in GF(2)^i is
    1+(2^i-1)+(2^i-1)(2^i-2)/6.
The last term counts independent ordered pairs divided by 6 bases per two-dimensional subspace. For i=0..4 the counts are 1,2,5,15,51. Thus five gates have 7650 dependency choices and 244800 output-mask templates, instead of 2^25=33554432 ordered choices. This is a roughly 137-fold reduction. If the last gate is absent from the output mask, it has no later reader and can be dropped, so those cases are covered by smaller t. Exactly 122400 five-gate representative configurations use the last gate and need direct evaluation.

## 2. Complete five-gate enumeration

The new checker uses exact square-free GF(2) ANFs rather than the preceding truth-table Mobius calculation for every template. XOR uses symmetric difference of supports; multiplication uses support union and parity cancellation. For each H, the mixed translation coefficient matrix indexed by nonempty subsets I,J has entry h_(I union J) if I,J disjoint and zero otherwise. Construct rows as BigInt bitsets by enumerating proper nonempty subsets of every ANF monomial. Perform GF(2) elimination with fixed lowest-bit pivots. The generic coefficient matrix is alternating, so its rank is even. The checker independently evaluates truth tables from the ANF and computes the anchored translation matrix on selected cases, including every last-used representative at t<=3 and periodic samples at larger t. It asserts complete canonical subspace counts, exact configuration counts, and observed maxima.

    t | last-used templates | skipped last-unused | maximum | direct matrix cross-checks
    1 | 1                   | 1                   | 2       | 1
    2 | 4                   | 4                   | 6       | 4
    3 | 40                  | 40                  | 14      | 40
    4 | 1200                | 1200                | 30      | 1
    5 | 122400              | 122400              | 62      | 30

Total 123645 evaluated last-used representatives across the five sizes; 76 direct cross-checks. The skipped last-unused representatives are covered by induction on gate count, including zero output. All assertions passed. At t=5 exactly 52992 last-used representatives attain rank 62. The replay emits full rank histograms and maximum per dependency-rank profile. These counts weight the canonical representatives, not all original ordered circuits. Earlier t<=4 results have an independent checker using truth-table Mobius ANFs and operand-swap reduction.

Thus R_max(5)=62, sharp by the previous chain construction or record-max template. The all-t conjecture R_max(t)=2^(t+1)-2 is now established through five gates by complete finite computation and for rank-one dependency circuits by the earlier paper theorem. Still no proof or exhaustive enumeration for arbitrary t>=6. No claim that the rank-maximizing topology is unique.

Run node five_mixed_rank_subspace_check.js. Checker body executed in the JavaScript tool runtime (not separately in Node or Lean). Commit 1c15d8adb490cc45fcf7c782b9efeee2b59ddd6e.

## 3. Exact final-gate identity

Let a,b be the final two fresh variables, and U,V,W be any Boolean functions of the n old lifted variables vanishing at zero. In the generic circuit they are GF(2) linear combinations of earlier gate outputs; all earlier gate outputs vanish at the all-zero lifted input. Assume final gate included in output, so

    H=(a+U)(b+V)+W = h+a V+b U+ab, h=UV+W.

Write M(f) for the full translation coefficient matrix on all old subsets, including empty; C(f) for its nonempty-row/nonempty-column submatrix; c(f) for the column of nonconstant ANF coefficients. M(1)=e_empty e_empty^T. In order of fresh subsets empty,a,b,ab, the full matrix M(H) is

    [ M(h)  M(V)  M(U)  M(1) ]
    [ M(V)  0     M(1)  0    ]
    [ M(U)  M(1)  0     0    ]
    [ M(1)  0     0     0    ].

This follows directly by disjoint splitting of monomial supports, without rank relaxation.

Take the four rows/columns whose old subsets are empty. Because h,U,V vanish at zero, the principal pivot block has exactly the two symmetric pairings empty<->ab and a<->b. It is invertible and equals its inverse. After eliminating these four pivot directions, the block for fresh subset ab and nonempty old subset is zero. The remaining Schur complement in fresh order empty,a,b is

    [ A     C(V)  C(U) ]
    [ C(V)  0     0    ]
    [ C(U)  0     0    ],

where A=C(h)+c(U)c(V)^T+c(V)c(U)^T. Indeed the coupling of an old nonempty index in the fresh-empty block to the four pivot indices is (c(h),c(V),c(U),0) coordinatewise; those in fresh-a and fresh-b blocks couple only to pivot empty by c(V) and c(U), respectively. The pivot inverse gives just the two outer products in the fresh-empty block. All signs are plus in GF(2).

Let B=[C(V) C(U)] horizontally concatenated; r=rank B, equivalently rank of the vertical stack by symmetry. K=ker B^T=ker C(V) intersect ker C(U). Let s be the rank of the alternating bilinear form A restricted to K, i.e. rank of E^T A E for any matrix E whose columns are a basis of K. The bordered matrix [[A,B],[B^T,0]] has rank 2r+s: choose a complement to K on the first space and a corresponding r-dimensional subspace on the second on which B pairs nondegenerately, together with ker B. Eliminate the paired 2r directions. The block on K is unaltered (its coupling to the paired second directions is zero, and the inverse paired block has zero first-first block). The ker B directions are zero. This is a standard block rank identity, applied here to the actual translation coefficients. Hence full translation rank of H is 4+2r+s.

H is nonconstant since its ab coefficient is 1. As proved in the preceding handoff, nonconstant full translation rank is mixed rank plus 2 (border by nonconstant coefficients, which are outside the mixed matrix column space as witnessed by a maximum-degree monomial). Therefore

    R_mix(H) = 2+2r+s.

This is exact, including for actual generic dependencies of rank two and arbitrary earlier-output mask W. It does not assert that r or s is easy to compute for exponentially many lifted variables.

For the conjecture at t gates, the exact final-gate reduction for every last-used generic template is to prove
    2r+s <= 2^(t+1)-4.
Last-unused masks are handled inductively. Neither term should be bounded independently and then charged as new physical gates. The previous recurrence used common factor-space rank and lost this residual form; no proof of the displayed inequality for arbitrary t is claimed.

## 4. Residual is real, not an artifact

For W=0 and V=0, K=ker C(U), A=0, s=0 and R_mix(H)=2+2 rank C(U). This reproduces the sharp chain recurrence exactly. For two independent preceding seeds U=z1*z2 and V=z3*z4, W=0, the final rank-two merge has r=4 and s=4, giving mixed rank 14. Dropping s would falsely predict 10. More generally when U and V use disjoint old variables and W=0, H factors over disjoint coordinates as (a+U)(b+V); full translation matrices tensor, so their ranks multiply. If each branch has p and q mixed gates respectively and satisfies the conjectured full rank ceiling, then the combined circuit with p+q+1 mixed gates satisfies it too. Addition of a fresh affine variable to a nonconstant U leaves its mixed translation rank unchanged, so its full rank unchanged; if U=0, the factor a has full rank 2. This conditional disjoint-branch induction does not cover overlapping branches or arbitrary W.

The regression computes C(U),C(V),A from ANFs, obtains an actual kernel basis via tagged GF(2) elimination of columns, computes rank of the restricted bilinear form by exact parity, and compares to direct full and mixed coefficient matrix ranks of H. Seed 870033: 240 pseudorandom generic preceding circuits (one to three preceding gates), four chain controls (one to four preceding gates), one two-seed merge; 245 cases. All assertions passed. Residual nonzero in 62 cases, largest observed s=12. For chains full ranks 8,16,32,64, s=0 throughout. The two-seed merge has r=4,s=4, full rank16. The largest residual case in replay has n=6,r=8,s=12, full rank32. These are exact tests of the identity, not evidence that s is universally bounded by 12.

Run node translation_last_gate_check.js (no dependencies). Checker body executed in JavaScript tool runtime, not separately in Node or Lean. Commit 7376215bc304d5dd7dd11d53ff83c1c564c74f98.

## 5. Shared-witness consequence and scope

For the abstract shared-witness F(H,S,Q)=OR_(j in Q) AND_(i in S) H_ij, exact mixed rank=(2^m-1)(2^ell-1). At m=2,ell=5, rank=93>62. Thus any circuit needs at least SIX syntactically mixed ANDs, even with arbitrary pure preprocessing. Earlier information bound gives five and full response span 94 passes the older 3^5=243 bound. Direct anchored truth-table replay confirmed rank 93 on all 131072 data/query assignments. This is a mixed gate lower bound for the abstract function, not a physical SAT encoding result for this small instance: ell=5 does not satisfy the earlier power-of-two packing hypothesis. No new grammar/padding replay and no unrestricted superlinear lower bound. For general valid packing parameters, earlier reductions may be combined only where their premises hold.

## 6. Next attack

Use the exact coupled inequality to control the residual on common kernels by earlier-gate resources; do not discard it or assume all factor products independent. Investigate whether earlier gate relations can furnish a rank certificate for the restricted alternating form, using disjoint merge and positive-residual cases as controls. A six-gate complete search grows substantially (dependency subspace count at i=5 is 187; 7650*187*32=45777600 last-used templates), so the proof route or further exact symmetry reductions are preferable to naive exhaustive growth. Independently audit subspace symmetry and Schur elimination; formalize simple lemmas before asserting a general theorem. No upstream submission or production modifications. L-clb-036 remains open.
