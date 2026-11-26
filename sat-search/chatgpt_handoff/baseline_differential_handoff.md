# Baseline-differential gate transversals

Date: 2026-11-26. Continues [response periods](response_period_handoff.md) and [stable gate roles](gate_role_ledger_handoff.md). Repository head observed before work: 0f4ccfc78c3f719117d416499f10f785c991a672 (native nine-gate certification also present). Paper proof and exact finite replays, not Lean checked or independently audited. No priority claim. L-clb-036 remains open.

## 1. Model and theorem

Use a finite Boolean XOR-AND circuit with free XOR, NOT, constants and fan-out. Contract affine wiring: each AND operand and the final output is an affine combination of primaries and earlier AND outputs. Data x and query q vary over a common full binary cube. Fix one baseline q0. Write delta f(x,q)=f(x,q)+f(x,q0) over GF(2). An AND gate is called mixed if its output function depends on both blocks SEMANTICALLY. Pure-data outputs have zero differential, and pure-query outputs have differential constant in x. This is a semantic certificate, not an efficient classification procedure for arbitrary circuits.

Enumerate the t mixed ANDs in original topological order. For each, let A_i=u_i(x,q0), B_i=v_i(x,q0) be its actual two baseline operand functions. For each fixed query q, the operand differences are affine in previous mixed gate differences with coefficients/constants in GF(2), since pure gate differences are constants. The exact identity is

    delta g_i = A_i delta v_i + B_i delta u_i + delta u_i delta v_i.

In particular A_i B_i cancels. Introduce independent formal Boolean variables a_i,b_i,y_i, representing A_i,B_i,delta g_i, with squares reduced to themselves. The formal expression for y_i is a_i times an affine expression in earlier y_j, plus b_i times another such expression, plus the product of those two affine expressions. No term contains both a_i and b_i. Start with the affine expression for the output differential in y_i. Substitute for y_i in descending topological order, reducing squares after each substitution. At the stage of eliminating y_i no a_i or b_i has yet appeared: substitutions for later gates introduce only their own baseline symbols. A square-free term contains y_i at most once; replacing it therefore introduces at most one of a_i,b_i. Subsequent substitutions introduce only earlier baseline symbols. The result is in the span of monomials choosing at most one symbol per pair. Evaluating formal symbols at the actual baseline functions proves

    delta F(.,q) in V = span_GF(2){ product_i Z_i : Z_i in {1,A_i,B_i} }.

This holds simultaneously for every q with the SAME baseline operands and original gate indices. Multiple outputs can use the same V. The same argument allows any common query domain containing q0, with pure/mixed classification valid on that domain. No assumptions on fan-out or circuit minimality.

## 2. Consequences

Let N_delta be the number of distinct joint differential signatures (delta F(x,q))_q as x varies. Let R_delta be the GF(2) rank of the differential family. Then

    N_delta <= |image (A_1,B_1,...,A_t,B_t)| <= 2^(2t)
    R_delta <= dim V <= 3^t
    deg delta F(.,q) <= sum_i max(deg A_i, deg B_i),

where constant and zero functions are assigned degree zero for bounds. The first inequality follows by reconstruction from the fixed baseline operand map, not from its polynomial coefficient rank. The second counts candidate products, not independent products. The third uses subadditivity of Boolean degree under multiplication. More sharply, for any specified data subset U, define deg_U as the maximum number of U variables in any ANF monomial. The identical argument gives deg_U(delta F) <= sum_i max(deg_U A_i,deg_U B_i). If a target monomial occurs, at least one term in some transversal product of baseline ANFs must have union of supports exactly that monomial's support. Thus gate-specific support certificates can reject candidates even when aggregate degree counts pass. The exact span and image may be smaller.

The bound t >= ceil(log2 N_delta / 2) allows arbitrary pure-side ANDs for free. It is tight as a general information bound: pair independent data bits a,b with query bits u,v. One mixed AND (a+u)(b+v), plus pure corrections ab and uv, produces av+bu. XOR such pairs; baseline zero, d=2t, all data signatures distinguishable. In particular, no universal stronger coefficient follows from injective signatures alone. For arbitrary F, the original response signatures need not be differential signatures: one extra baseline output bit may be needed (N <= 2 N_delta for a scalar output). Do not apply the bound to N without this adjustment unless a data-independent baseline or another injectivity argument is established.

The relation to prior periods is direct: apply the prior period certificate to the fixed baseline operand vector, which reconstructs every differential. It is a capacity upper bound, never a demand without separate residual evidence.

## 3. Exact affine-transversal degree cap

Suppose all baseline operands are affine in x. Write a_i,b_i now for their linear coefficient vectors in GF(2)^d (not the formal Boolean symbols above). Let r* be the maximum rank obtainable by selecting at most one vector from each pair. Then the maximum degree of any function in V is exactly r*.

Upper bound: every transversal product depends only on the linear forms in the selected vectors, so after factoring through a rank-r linear map it has Boolean degree at most r (substitution of affine forms cannot increase degree). Lower bound: choose r* independent vectors from distinct pairs. Their associated affine functions are jointly surjective. Their product has degree r* by extending the independent vectors to an invertible linear coordinate change and using degree invariance under invertible affine substitution. The empty product handles r*=0.

The standard independent-transversal theorem for a linear matroid (Rado's theorem, or matroid intersection of the partition and linear matroids) gives

    r* = min_(I subset [t]) (t-|I| + rank{a_i,b_i : i in I}).

This is the maximum independent partial transversal; an arbitrary rank-maximizing selection can be reduced to an independent one. The min-max expression is a classical theorem, not a new matroid result. A polynomial matroid-intersection implementation is possible given coefficient vectors; our small replay enumerates choices and subsets, not a scalable algorithm.

For a response of degree d, every gate subset I must satisfy rank{a_i,b_i : i in I} >= d-t+|I|. Even when t>=d and the global rank is d, a subset of gates can violate this. Example d=t=4: pairs (e1,e1),(e1,e1),(e2,e3),(e4,e4). Global rank 4, but r*=3. This is a candidate certificate; not every abstract pair profile corresponds to a circuit. For affine baseline operands, full-degree target demands t>=d, with no extra charge for evaluating the baseline because the argument is about actual fixed functions. No such conclusion holds for arbitrary nonlinear baseline operands. The affine assumption must be verified, not imposed on all minimum circuits.

## 4. Application to packed shared witnesses

Use the already established restriction F(H,S,Q)=OR_(j in Q) AND_(i in S) H_ij (see response_period_handoff.md for grammar, packing, exact rank proof and limitations). Choose S=empty,Q=empty at baseline, so F=0 independently of data. Let d=m*ell. Singleton row and column queries retrieve every bit. All-selected query has degree d: in the expansion 1+product_j(1+product_i H_ij), the full monomial occurs exactly once. The GF(2) response-span rank is R=1+(2^m-1)(2^ell-1). Therefore any XOR-AND circuit has

    t >= max(ceil(d/2), ceil(log_3 R)),
    sum_i max(deg A_i,deg B_i) >= d.

If baseline operands are affine, t>=d and r*=d; every subset rank condition in Section 3 holds. This is a genuine mixed nonlinear gate count, with no duplicated scenario charge. It does not imply superlinear size: the shared-witness promise itself has O(d) gates. The model relaxes the original signed AIG/general binary circuit model (any two-input Boolean gate is affine or one AND plus free affine operations), so a lower bound on t also bounds total original binary gates under that simulation, but semantic mixed roles after affine contraction need not coincide with original syntactic roles. No new grammar replay or SAT-wide asymptotic conclusion is claimed. Prior packing overhead and length restrictions remain.

## 5. Exact finite replay

Run:
    node baseline_differential_check.js
    node baseline_affine_transversal_check.js

Both checker bodies executed in the JavaScript tool runtime before upload; no separate Node process or Lean replay. Differential checker seed 870028: 250 circuits (240 pseudorandom plus 10 controls), 1198 query contexts, 4566 gate-differential checks, 38198 square-free transversal term checks, 1198 degree checks, 250 exact span checks. Enumerates all data and query assignments in each small case, computes semantic pure/mixed classification, checks actual baseline operands, symbolic differential identities and exact GF(2) span. All assertions passed. Random masks use high bits of the deterministic LCG; this is a regression, not an exhaustive classification of circuits.

Controls:
- Enabled AND on d=2,3,4,5 data inputs: t=d, baseline degree budget d, rank 1, two distinct data signatures.
- Paired inner products d=2,4: t=1,2 respectively, 3,6 total ANDs including pure corrections; 4,16 signatures.
- Shared witnesses (m,ell)=(1,2),(2,1),(2,2),(3,1): mixed AND counts 5,4,9,6; degree budgets 2,2,4,3; exact response ranks 4,4,10,8 and signature counts 4,4,16,8. These are explicit upper-bound circuits, not minimum gate counts.

Affine min-max checker seed 870029: 180 instances, 34932 transversal choices, 4008 gate subsets; equality in every instance, 20 strict deficits relative to min(t,global rank). This independently compares finite enumeration of the two sides of the classical formula, not a proof of the general theorem.

Checker commits d4eb41f67d9eb2f884cab73ecfb59470b94e521f and 9ee6e6726c8c019068f1b9e2bb38230376ebcb16.

## 6. Next attack and limits

The main obstacle is to control the baseline functions themselves. A nonlinear baseline may already contain difficult products and may be reused by many gates. Charging its degree multiple times as new work is invalid. Choosing a baseline that makes enough operands affine would be useful, but there is no general proof such a baseline exists. Also, allowing arbitrary pure-side preprocessing makes a one-bit query selecting any fixed data function cost just one mixed gate.

Next test: use multiple baseline queries and actual stable IDs, detect deficits with the exact transversal span or affine matroid cap, then investigate whether one can force a rank deficit for every low-size candidate without charging shared baseline gates more than once. A useful negative control is the paired inner product; a nonlinear baseline control should deliberately violate the affine conclusion. Compare with the earlier programmable permutation control rather than inferring any per-gate bound on unnormalized cofactor rank. Independently audit the reverse substitution in the Boolean ring and the semantic-to-syntactic model distinction. No claim of superlinear SAT gate complexity, no upstream submission, no production changes. L-clb-036 remains open.
