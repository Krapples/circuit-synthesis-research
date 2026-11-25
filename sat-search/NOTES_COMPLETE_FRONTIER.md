# Complete-function frontier and algebraic reconstruction

*November 24, 2026*

## Complete-function FPT audit

The three supplied programs were used as comparison subjects. The independent implementation is
[complete_frontier.py](experiments/complete_frontier.py). It emits a gate program and checks two
different costs. The monotone basis charges only binary gates. The signed basis charges every
NOT. For $m$ essential inputs, $e$ excess reads and $q$ unary gates the total is
$m-1+e+q$. All claims here concern complete, explicitly supplied truth tables.

Cut a connected circuit at repeated wires. Each region is a read-once tree on private
primaries and input port occurrences, with unary nodes allowed in the counted-NOT version.
Order the regions from providers to output. At a frontier, fix the processed primary set $X$,
the number of remaining reads of each produced provider, and the reachable provider patterns.
For each such pattern store the cofactor on the as yet unprocessed primaries. Any two
assignments to $X$ realizing the same pattern must have equal cofactors, since the suffix sees
only the remaining ports and unprocessed primaries. Conversely the state defines exactly what
the remaining regions must compute. If a provider has no unread occurrences, forget its bit.
Reject a collision with unequal cofactors and merge a collision with equal cofactors.

For each old pattern, assigning the next private group can produce at most two different
cofactors. With two residuals the next provider must be their exact selector, up to complement
in the signed problem. With one residual there are three possibilities for the provider slice:
constant zero, constant one, and nonconstant. The two slots of a nonconstant selector are
reachable because the target is complete. Unreachable patterns remain absent.

The local completion splits leaves into two disjoint parts or spends a NOT on the root. A
nonconstant exact slice of an AND or OR determines each child's restriction by existential or
universal elimination of the other child's primaries, respectively. In a fixed port context,
the path from a subtree to the root applies unary negations and combines with siblings fixed
to constants. Each nonconstant cofactor on the subtree's primaries is therefore the same
function up to complement. This justifies the finite canonical slice states. For a constant
or a nonconstant wildcard, the neutral and absorbing alternatives implemented by the local
solver exhaust all feasible child-status pairs. A NOT complements exact obligations, preserves
wildcard status, and consumes one unit from the shared unary budget.

If the allowed overhead is $s$, at most $s$ provider bits survive, total port occurrences
are at most $2s$, and the possible degree vectors and unary allocations depend on $s$ alone.
For any fixed $X$ the search rejects more than $2^s$ distinct target cofactors. A residual
vector therefore has at most $(2^s+1)^{2^s}$ choices. Each local subtree state has a bounded
alphabet per reachable slice and at most $m+2s$ leaves to choose from. Enumerating group
choices and local splits and operating on the explicit truth tables costs $g(s)L^{O(1)}$,
where $L=2^m$. The polynomial exponent is independent of $s$. This proof uses complete
cofactors and leaves the partial-label hardness result intact.

The audit compared both supplied solvers and the constructive implementation with independent
gate-program enumeration on 1,063 complete-function budget decisions. A separate oracle
enumerated concrete multislice tree tables on 540 queries, including counted NOTs. All
constructed witnesses were evaluated on every row. The primitive assumes nonconstant
targets with essential declared primaries.

The 82-job profile compared the frontier solver with the repository truth-table SAT encoder.
Cross-region local caching reduced local states from 10,543 to 9,503. Forgetting exhausted
provider bits merged 158 patterns and reduced local states versus the uncompressed variant,
while its wall time rose from 0.199 to 0.222 seconds in this sample. Direct SAT took 0.437
seconds. A 60-state frontier cap with SAT fallback took 0.314 seconds and fell back on 19
jobs. The comparison is a small feasibility check for a hybrid. [Raw audit](results/complete_frontier_audit.jsonl)

## The guarded rank-tight family

Use $W(v)=b\lor (a\land(c\lor v))$ with a fresh triple per use. Make a chain of $e-1$
inner wrappers ending at a primary. Each chain terminal has one outer wrapper, and the top
terminal has a second. The output is the OR of that second wrapper and the AND of the
other outer wrappers. There are $6e+1$ essential inputs and $7e$ binary gates. Each chain
terminal has exactly two readers. Private bypass and witness terms check essentiality,
including the $c$ inputs that need not occur in the rank minor.

At the top terminal, choose positive certificates that read exactly one of its two
branches, and negative certificates that visit the respective terminal reader and stop
the other branch with private zeros. The two membership patterns yield the off-diagonal
two-by-two block of the certificate intersection contribution.
At every deeper terminal choose a chain-only, direct-only, and both-read certificate on
each axis. To obtain these positive certificates, request the previous outer guard and
recurse, request the current outer guard, or do both. Bypass unrelated outer guards and
stop at the chosen stage. For the negative certificates, the second top wrapper can
follow the chain, and the negative certificate of the AND branch can stop an unrelated
path or request the current guard's source. It uses the private zero pair to stop any
branch whose source should be absent. Removing a listed bit changes the corresponding
branch obligation, so these are minimal certificates.

In both axes each of these choices has no active repeated reads deeper than its chosen
terminal. Their membership matrices are triangular by depth, with identity blocks of sizes
two and three. A binary repeated wire contributes the matrix with ones at (chain, direct)
and (direct, chain), and minus one at (both, both). These blocks are invertible modulo two.
The selected minor is the product of the two triangular matrices and these full-rank
blocks. It has rank $3e-1$. The general $3e-1$ bound gives equality and forces at least
$e$ excess reads, proving an exact optimum of $7e$ gates.

At $e=2$ the rank is five, so the universal $2e$ conjecture is closed. The regression builds
explicit certificate minors through $e=12$ and independently verifies their minimality;
the full truth tables are checked at $e=1,2$. [Regression](experiments/rank_tight_family.py)

## Typed affine ranks and completion

An AND root takes products of its children's positive certificate families and disjoint
unions of their negative families. An OR root reverses those roles. Affine dimensions add
on products. For disjoint union the dimensions add with one extra per binary union;
each child's affine anchor is outside its direction space because every opposite
certificate has scalar product one with it. Induction gives positive affine dimension
equal to the number of OR gates and negative affine dimension equal to the number of AND
gates in a read-once region. Taking a subset of observed certificates and projecting to
primaries preserves the lower-bound direction. Empty projections are included at the
output or when a visit is known.

`--certtyperank` converts the two local ranks into a port count when they require more
gates than the private leaves supply. It also minimizes typed sums over ordered primary
groups and combines the results with the whole-function certificate count bounds. This
uses cached ranks modulo 2 and 101. Among 56 complete targets with at most six inputs,
950 regional pairs had a nonzero rank. The strongest matched port-cost reference already
covered every converted regional cost and every whole-function lower bound. Setup was
0.244 seconds versus 0.191 seconds. The option remains experimental.

`--affinecompletion` treats fixed rows as exact terminal certificates and first checks
all cross intersections. Over GF(2), $U_0$ is contained in the orthogonal complement
of the span of the prescribed negatives; the quotient dimension is the deficit. For
each small quotient subspace, lift $U$ and recover $V=\operatorname{span}(U,p_0)^\perp$.
RREF supports give the finest coordinate components. In an alternating cotree, the
positive space splits at an AND root and the negative space splits at an OR root.
In the other space, differences linking certificates of different children connect
their supports. A proper coordinate split would have a component projection that
violates orthogonality with an opposite certificate. Recursively restrict both spaces,
then verify every original certificate directly.

The lazy backend uses a verified full-tree completion as a shortcut and keeps the
existing compatibility fallback. A failure of exact completion does not exclude a
partial truth-table query or an at-most model that can drop leaves. Independent
cograph enumeration agreed on 750 fixed-family queries. The seven-budget backend
ablation substituted affine reconstruction in 56 regions, all at zero deficit.
Conflict and clause counts did not change. Totals were approximately 1.59 seconds
with the one timeout in every variant. [Ablation](results/regional_algebra_ablation.jsonl)

Rational affine-basis compression is sound for fixed exact rows. The rational
affine hull of a read-once certificate family meets the Boolean cube exactly in
that family. For a product, use induction on the factors. For a disjoint union,
the coefficients of each child block sum to a nonnegative integer because
intersecting with any opposite certificate of that child returns the coefficient.
These integers sum to one. A zero-coefficient block vanishes since each coordinate
is covered by an opposite certificate. The unique coefficient-one block meets
its child's affine hull and the Boolean cube. This argument does not apply over
GF(2). The three singleton rows span the triple row affinely modulo two.
The 750-query differential replay reduced 35 fixed families while preserving
feasibility. No symbolic global certificate rows are compressed.
