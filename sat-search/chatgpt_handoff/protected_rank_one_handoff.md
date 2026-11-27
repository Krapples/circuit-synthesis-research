# Protected rank-one elimination and exact potential deficit

Date 2026-11-26. Continues protected_parameter_elimination_handoff.md. Paper local move and finite regression; no new unconditional size bound, Lean verification or production change.

## 1. Local move

Use the prior fair affine system, disjoint data pairs constrained by product zero, and protected query parameters y. Let d be the data parameter count, h the number of pairs, a=d-h. Let I_D count used unpaired data parameters, s count affine equations and binary gate units. W=s+4h+6I_D.

Consider a proper minimal AND-type binary gate G with two affine operands, with rank one of their linear parts on unpaired data columns. At least one operand L has a nonzero unpaired data coefficient. Choose its input phase so that G=(L AND M) XOR gamma. Promote L to a data parameter using the previous fair-system exchange (or use it directly if it already is an unpaired data parameter). Fix L=0. This is an affine restriction of the parameter domain, preserving all query variables and existing paired coordinates. Every setting of the remaining coordinates uniquely determines the old pivot, even if L depends on protected query or paired variables. The data map remains injective and every query remains available. No arbitrary affine circuit is inserted: the actual operand is fixed, with the affine equations retained and simplified. In a uniquely solvable affine system, fixing a parameter preserves uniqueness for the remaining parameters; removing redundant terms or constant aliases must preserve this property.

G becomes constant gamma. For a live nonoutput G, at least one distinct binary successor becomes constant or unary. Remove these two gate units, substituting the corresponding literals or constants; no new binary gates. If G is output, the earlier relative degree lemma excludes the case when a>2ell. This claim assumes the usual acyclic binary part and a successor in it, not an arbitrary affine equation feedback graph with nonlinear gates. Existing paired constraints are untouched. I_D decreases by at least one: the pivot was used (nonzero coefficient in an actual operand), the promoted operand is then fixed, and substituting a unary successor cannot make an unused unpaired parameter used. The other operands were already present. Equation simplification may yield additional savings; none assumed.

Hence Delta a=-1, Delta h=0, Delta s<=-2, Delta I_D<=-1 and Delta W<=-8. This is also an available fallback for rank two, although the pairing move is stronger there. For rank zero on the unpaired data columns this argument does not apply. If G has no remaining live successor because of earlier pruning, remove it as dead instead, not as a two-gate charge.

## 2. Deficit accounting

For a sequence of R rank-one fixing moves and P rank-two pairing moves, with any additional steps assumed not to increase W or change a, we obtain
    W_final <= W_initial - 8R -10P
            = W_initial -10(D-a_final)+2R.
Here a_initial=D, assuming no initial pairs. Equivalently the amended potential W-2R satisfies the desired ten-unit drop, but R is a cumulative penalty, not a free nonnegative potential. If the process actually terminates at a_final<=2ell and W_final>=0, then with W_initial<=B+encoding_cost+6D,
    B >= 4D-20ell-2R-encoding_cost.
This is CONDITIONAL on completing the process, not a proved SAT lower bound. A bound R=o(D) would recover the leading 4D coefficient on the data slice, still below the existing full physical SAT bound due to layout overhead. A guarantee of all rank-one/two moves only would give at best 2D-O(ell)-encoding_cost, not a new result of interest. Do not assume such a sequence exists: rank-zero gates and other minimal configurations can block it.

## 3. Why sacrificing query dimensions needs a separate invariant

Full query projection is preserved by the rank-one fixing move, so no relaxation is needed for that case. Rank zero is harder. Merely retaining a query affine subspace of codimension one does not ensure any useful selector contexts: fixing p=0 eliminates unit mode completely. Even retaining p=1 is insufficient with arbitrary constraints and data fibers: e.g. force two selected slots whose lambda dot values are opposite for the chosen coordinate dictionary, making every selection containing them false. One cannot replace full projection in the relative degree proof by a dimension count alone without controlling available selector supports, dictionary directions and data offsets. Retaining an appropriate hard-mode point is also not equivalent to preserving hard-mode complexity. The previous small selector-only upper circuit remains a negative control for any proposed full potential argument.

Next: classify rank-zero affine parents involving protected queries and paired variables, and look for a semantic hard-mode invariant that allows a profitable alternative move, or a bounded deficit proof with explicitly preserved query contexts. Do not claim progress toward a superlinear recurrence merely by counting the cumulative deficit.

## 4. Regression

protected_rank_one_check.js commit 1a168d015ea089a1daaa09c110ed2e2e2b9582e8, seed 870067. Executed in JS tool runtime. 1200 affine operand profiles: 561 rank one, 517 rank two, 122 rank zero. 21920 controlling-value, injectivity, protected-query and output preservation evaluations; 16008 with paired constraints; 1000 numerical deficit-ledger checks. All assertions passed. Checks use explicit affine maps and an XOR child, not a full fair-system circuit algorithm, arbitrary child enumeration or an independent proof audit. Prior fair-system exchange proof is reused. No Lean build, new physical grammar, numerical full-SAT lower bound, production edits or upstream submission. L-clb-036 remains open.
