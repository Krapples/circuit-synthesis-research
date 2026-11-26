# Two-sided degree-rank frontiers with once-only pure gate substitution

Date 2026-11-26. Extends [baseline differentials](baseline_differential_handoff.md) and [multi-baseline intersections](multi_baseline_transversal_handoff.md). Starting head observed 40132e10aac5b35fd32bc70330502db7c6715212; native agent's L-meta-16102 gap survey also present. Paper proofs and finite exact replay, not independently audited or Lean checked. No priority claim, production change or upstream submission. L-clb-036 remains open.

## 1. Model and once-only substitution

Use XOR-AND circuits with free XOR, NOT, constants and fan-out. Contract affine wiring into affine expressions in primaries and earlier AND outputs, reducing identical terms. Classify AND gates by SYNTACTIC transitive ancestor support in these expressions: data-only (a gates), query-only (b gates), mixed (t gates). Constant-only gates can be evaluated and eliminated. The pure gates of either side have no mixed ancestors. This qualification is essential; a semantically pure gate with mixed ancestors cannot simply be counted as a pure-side preprocessing circuit. Previous semantic mixed count can be smaller than t. Bounds on syntactic t do not imply the same bound on semantic t.

Introduce one independent formal variable for each pure-side AND output, keeping the raw primary inputs. Each mixed operand is an affine combination of lifted data variables X, lifted query variables Y and earlier mixed gate outputs. Let u be the rank of the 2t data linear ingress forms in X and v the rank of the 2t query linear ingress forms in Y (constants removed). Thus u<=min(2t,d+a), v<=min(2t,k+b) for d data and k query primaries. Choose independent forms as coordinates U,V respectively. The mixed gate recurrence now has t ANDs on formal coordinates U,V; the affine output may include other pure terms, which have no mixed ANF coefficients. Treat U,V as independent for this formal circuit, even when actual values after preprocessing have relations.

The formal output polynomial G(U,V) has total Boolean degree <=t+1, by substituting AND variables into the affine output in reverse topological order. In the Boolean ring each square-free monomial contains a variable at most once; a substitution of a product of affine forms increases degree by at most one, regardless of fan-out. This is the standard multiplicative-complexity degree bound. Discard pure-side terms when considering mixed coefficients.

Substituting U,V as affine forms in the lifted X,Y cannot increase the corresponding side degrees. Now substitute each of the a data-only gate variables by its product of affine operands in reverse topological order, and similarly for the b query-only gates. A monomial of U-degree i and V-degree j becomes a polynomial with data degree <=i+a and query degree <=j+b. Each distinct pure gate is charged at most once in this substitution, not once per occurrence, product factor, or baseline. A term with i=0 or j=0 stays pure, and cannot contribute to a mixed coefficient. Thus a mixed target monomial of degrees r,s>=1 requires

    L+M <= t+1, L=max(1,r-a), M=max(1,s-b).

This also recovers the global degree bound a+b+t>=r+s-1, and two separate constraints a+t>=r, b+t>=s. It is not in itself a stronger general total gate lower bound than ordinary joint degree.

## 2. Two-sided rank frontier

For the actual target F(x,q), let C be its GF(2) ANF coefficient matrix indexed by data monomials and query monomials. Let R_(r,s) be the rank of the submatrix with row degree>=r and column degree>=s, r,s>=1. It excludes all pure terms. It equals the rank of the corresponding doubly degree-projected mixed polynomial tensor.

Before substitution, the formal mixed coefficient matrix has row degrees i>=1, column degrees j>=1 and zeros whenever i+j>t+1. Pure substitution is linear on the space of Boolean functions on each side separately, so actual coefficient projection is obtained by left and right linear maps applied to the formal coefficient matrix. By Section 1, only rows i>=L and columns j>=M can contribute to the projected actual tensor. Rank cannot increase under left/right multiplication. Cover the nonzero entries of the truncated formal matrix with all rows of degree i<=h and all columns of degree j<=t-h: any uncovered row has degree>=h+1, forcing every nonzero column to degree<=t-h. Splitting into matrices supported on these rows and columns proves

    R_(r,s) <= min_(0<=h<=t) [sum_(i=L)^h binom(u,i) + sum_(j=M)^(t-h) binom(v,j)].

Binomial coefficients outside 0..dimension and empty sums are zero. The endpoints give the one-sided truncated dimension bounds; interior cuts may improve both. This is the ordinary row/column cover rank bound applied to the degree staircase and actual lifted ingress ranks, not a new matrix rank theorem. It is a necessary condition, not a claim that every permitted coefficient matrix is realizable by t gates. Can combine with prior 3^t full response-span bound, ordinary residual counts and actual multi-baseline intersections; never add overlapping ranks as gate counts. Computing u,v is cheap given contracted expressions, but exact actual R may require expensive ANF evaluation.

## 3. Strict improvement over earlier aggregate span bound

With t=2, u,v<=4, the h=1 cut gives R_(1,1)<=u+v<=8, while the prior general response-span bound is 3^2=9. Separate one-sided bounds at u=v=4 are 10. This is a strict general mixed-rank improvement over the earlier scalar rank cap, in the syntactic model, without assuming anything about the pure side budgets.

Explicit target: four data bits and four query bits. Let A be the nine distinct monomial supports represented by masks 1,2,4,8,3,5,9,6,10 (four singleton and five pair supports). Define F(x,q)=XOR_(J in A) x_J q_J. Both zero baselines give zero; the coefficient matrix has nine independent diagonal entries, rank 9. Each side has 16 residuals, by singleton queries/inputs. Its total degree is 4. The hypothetical profile a=b=1,t=2 passes the ordinary degree bound (total 4 ANDs vs demand 3), both directional information bounds (4 bits vs 2t=4), prior full response-span cap 9, separate lifted rank caps 10, and bidegree frontier. But the new interior cut rules it out; indeed every circuit in the syntactic model for this F needs t>=3, regardless of pure-side budgets. This does NOT imply semantic mixed count>=3, or minimum total size, or that earlier exact per-candidate multi-baseline certificates cannot also reject such a circuit. This is a comparison with the earlier universal scalar cap.

## 4. Exact shared-witness SAT spectrum

Keep the previously established packed restriction F(H,S,Q)=OR_(j in Q) AND_(i in S) H_ij, with m rows, ell columns, d=m*ell data variables and k=m+ell query bits. Let S_i,Q_j denote Boolean selection bits; for a set J write S_J=product_(i in J) S_i, similarly Q_T. Over GF(2), using Boolean idempotence,

    F = XOR_(nonempty T subset [ell]) Q_T * product_i (1+S_i*(1+product_(j in T) H_ij))
      = XOR_(T nonempty, J subset [m]) H_(J x T) Q_T S_J product_(i notin J)(1+S_i).

Proof: express OR of selected column terms as sum of all nonempty products. For a fixed row, product over selected columns of (1+S_i*(1+H_ij)) is 1 if S_i=0 and product H_ij if S_i=1; hence the first identity. Expanding by row choices gives the second. Terms J=empty are pure query terms and share the empty data monomial. Every nonempty J,T gives a distinct rectangle monomial.

For fixed T with |T|=j, the mixed coefficient block has rows J with |J|>=max(1,ceil(r/j)), columns I subset [m] with |I|>=max(0,s-j), entry 1 iff J subset I. Column sets for different T are disjoint. Nonzero columns must have |I|>=max(1,ceil(r/j),s-j). On these columns take rows J=I; inclusion matrix is triangular in cardinality order, with unit diagonal. Hence rank equals exactly the number of such columns. Summing gives

    R_(r,s) = sum_(j=1)^ell binom(ell,j) * sum_(i=max(1,ceil(r/j),s-j))^m binom(m,i).

For r=s=1 the mixed rank is (2^m-1)(2^ell-1), one less than the previous full response rank due to omission of the pure-query component. For r=d,s=k rank is 1, with full joint monomial present. The ordinary degree bound therefore yields a+b+t>=m*ell+m+ell-1 for the abstract restriction; because the physical encoding fixes all other coordinates and may invert selected row polarity bits, this also applies to the packed SAT circuit at those lengths. Invertible affine polarity flips preserve total degree. Length remains Theta(m*ell) in the earlier packing regime; no superlinear asymptotic conclusion. No new grammar replay.

## 5. Experiments and negative result

Run node two_sided_degree_rank_check.js and node two_sided_degree_rank_controls.js. Both bodies executed in the JavaScript tool runtime before upload; no separate Node or Lean process.

Main replay seed 870031: 300 pseudorandom XOR-AND circuits and one explicit repeated-preprocessing circuit (301 total), 1525 degree-rank thresholds, 545 zero capacity thresholds, one interior cut strictly smaller than both endpoints. Exact ANFs computed by full Boolean Mobius transform. All assertions passed. Shared control has 5 data,4 query,4 pure data ANDs,4 mixed ANDs, ingress ranks 4,4; every mixed AND reuses the same degree-five pure conjunction. The previous sum of baseline operand degrees is 20 at zero query while the once-only data degree budget a+t=8 (actual data degree 5). With d data and t such gates, the old sum can be d*t whereas the new bound d-1+t counts the conjunction's d-1 gates once; no claim that the new bound is always smaller or tight. Nine complete rectangular witnesses m,ell=1..3: all ANF coefficients independently compared against the formula and all 168 positive degree-threshold ranks matched, including top mixed degree. Largest table has 32768 assignments.

The initial abstract split-profile search returned three exclusions including m=ell=2,t=2,a=2,b=3,u=v=4 with mixed rank demand 9 vs cap 8. This is NOT an improvement over all prior bounds: its full response rank is 10, already exceeding 3^2=9. Supplemental scan explicitly retained that older full-span requirement, t>=ceil(m*ell/2), the full joint degree frontier and ingress ranks u=m*ell,v=m+ell, over m,ell=2..5, t<=12, a<=m*ell,b<=m+ell. It tested 5158 qualifying profiles and found zero cases with a joint cut failure passing both separate cut bounds. This is a restricted finite negative result, not a theorem that the new constraint never improves any shared-witness profile. Supplemental checker also verifies the strict general nine-monomial example by 256 truth-table assignments and a Mobius transform. No claims of a new SAT-specific minimum size from the rank cut.

Checker commits c4265c43372f4b895cb5fd912c81fd1a98e755ea and c0c21e82574daa50c66ba37acf76b571f63e05e2.

## 6. Next research

The new frontier eliminates double charging of pure-side computations and gives a richer exact target profile. Its weakness is that the degree staircase forgets which mixed gates can generate which matrix entries. Next attempt should use actual stable mixed gate dependencies to restrict the formal coefficient matrix before pure substitutions, perhaps using a cut of intermediate gate variables and the ranks of their ingress subspaces. Look for a provable stronger support pattern rather than summing multiple scenario ranks; check against the paired-inner-product, programmable-permutation and multi-baseline tensor controls. Independently formalize the basic degree-substitution lemma and audit the syntactic/semantic distinction. L-clb-036 remains open.
