# Shared dictionary frontier partition products and telescoping gate ledger

Date: 2026-11-26. Continues multiport_residual_reserve_handoff.md (237e505). This note completes the interrupted handoff after the two checker commits below. Paper proofs, no independent audit, Lean verification, production change or unrestricted superlinear bound. L-clb-036 remains open.

## 1. Exact cell partition capacity

Target F(x,h,j)=h(x_j), m independent slots x_j in [P], P=2^ell, arbitrary shared Boolean table h, independent selector j in [m]. This is the unit-mode singleton-slot dictionary subfamily of switchable_incidence_handoff.md, with tags chosen by j alone and table signs by h. No new physical encoding or padding replay.

Take a topological prefix, c data-dependent frontier signals including bypassed primaries, q distinct query-only sources entering the data-dependent prefix. Their joint code is A(h,j). Let q_s count sources that depend on selector j (a syntactic upper bound is sufficient), so at most 2^q_s codes per fixed h. For each code a and slot j put T_(a,j)={h:A(h,j)=a}. Partition [P] by agreement under every h in T_(a,j); r_(a,j) is number of equivalence classes, 1 if empty. |T_(a,j)|<=2^r_(a,j).
If two data assignments have the same frontier value under code a, then every output h(x_j) for h in T_(a,j) agrees. Their slot values thus belong to identical class tuples. Every class tuple is possible by data independence. Consequently
    product_j r_(a,j) <= |image H_a| <= 2^c.
A canonical mixed-radix index of the class tuple suffices at the abstract encoding level. No Boolean gate efficiency follows.

## 2. Selector-free and mixed tradeoffs

If q_s=0, every realized code has the same partition for every slot. Thus r<=floor(2^(c/m)), and counting dictionary tables gives q>=max(0,P-floor(2^(c/m))). A nonconstant h has at least two classes, so c>=m regardless of q. With no ingress c>=m ell.
For separable A=(U(h),V(j)), with q_h and q_s wires, choose a selector cell of g>=ceil(m/2^q_s) slots and a dictionary cell of >=2^(P-q_h) tables. Then c>=g log2 max(1,P-q_h), or q_h>=max(0,P-floor(2^(c/g))). Also c>=g by using a nonconstant h. This needs separability, not merely a count of mixed sources.
For k raw dictionary entries and no selector, the worst class count is exactly P-k+min(2,k): unread entries separate and read entries have at most two fixed values. Both values attained for k>=2. Hence exact abstract width ceil(m log2(P-k+min(2,k))).

For arbitrary mixed ingress fix any nonconstant h. Some code is used by >=ceil(m/2^q_s) selectors, each with r>=2; thus c>=ceil(m/2^q_s). More generally for integer 2<=t<=P call a cell high if r>=t. At most floor(c/log2 t) high slots per code. For any fixed h, at least L=m-2^q_s floor(c/log2 t) selectors lie in low cells. If L>0, count the same (h,j) pairs in two ways: at least 2^P L, at most 2^q m 2^(t-1). Hence
    q>=max(0,ceil(P-t+1+log2(L/m))) when L>0.
Maximize over thresholds and the previous scalar floor, not sum. Corollary if q<=P-t then c>=m log2(t)/2^(q_s+1), including the case L<=0. The scalar residual count for this target is exactly 2+m(2^P-2).
Example m=64,ell=8,c=512,448,384,256,128,64 gives selector-free q>=0,128,192,240,252,254; c<64 impossible. The subsequent private-compression handoff strengthens the selector-free bit floor by one when 2<=r<P.

## 3. Exact incremental original-ID gate ledger

In a live proper signed AIG, process data-dependent gates in topological order. d essential data primaries initially on frontier. B_i processed gates; c_i processed data-dependent vertices (including primaries) with unprocessed consumers, or the output; Q_i query-only operand OCCURRENCES; q_i distinct query-only sources seen; e_i processed data operand occurrences minus number of retired data-dependent vertices. All Q,q,e nondecreasing. An occurrence consuming a nonfinal use increments e; a final use retires its vertex, giving no e increment. Output has permanent virtual final use, not a processed occurrence. Each new data-dependent gate has at most one query-only operand. Exact
    B_i=d-c_i+Q_i+e_i.
If r operands retire, c increments 1-r and Q+e increments 2-r. Thus for any nested prefixes u<=v,
    B_v-B_u=c_u-c_v+(Q_v-Q_u)+(e_v-e_u)
              >=c_u-c_v+q_v-q_u.
This counts disjoint actual gate IDs, not overlapping cone lower bounds. A lower floor L_v on q_v gives >=max(0,c_u-c_v+max(0,L_v-q_u)). Pair-complete data additionally e_v>=max(0,d-c_v) by first-branch separation. If e_u known, insert max(0,d-c_v-e_u) as an additional e increment lower bound. Subtracting two lower bounds is invalid; need an actual earlier value or upper bound. Width differences may be negative; do not take absolute values or sum full prefix bounds.

## 4. Controls and barrier

Selector-first mux tree for m=2^k: select ell coordinate bits via 3ell(m-1) signed ANDs, width ell, ingress k selector bits; one shared table mux costs 3(P-1) more. Dictionary-first evaluates all slots separately via 3m(P-1) ANDs, width m, ingress P table bits, then 3(m-1) for selection. Thus no universal mP charge for this target. The physical tag selection can also be decoded and the unique active slot selected efficiently on the promise. No upper bound for full SAT inferred. Exact ledger enables disjoint charges but does not establish growing gate cost per physical input.

## 5. Executed regressions

selector_dictionary_frontier_check.js commit 1234f475c9679b425ea238c4edcbe1c725f347e5, seed 870055: 192 abstract code profiles, 5959 realized cells, 16476 partition checks, 14646016 output reconstruction checks, 72 threshold checks, 34 exact raw-entry profiles. 23 strict improvements over scalar floor, 146 selector-dependent profiles. Abstract mixed-radix encodings, not cheap circuit synthesis. frontier_increment_ledger_check.js commit 8fc0bfb663a71ae84fc136ad0a2123d04d8bca96 seed 870056: 1200 random DAGs pruned to live output, 18 explicit order controls, 4086 data gate stages and random intervals, 1079 fanout increments, 2035 metadata occurrences, 1572 width decreases, 600 increases. Both bodies ran in JS tool runtime; not independently Node/Lean. All assertions passed. No native benchmark. This file was not committed before interruption; the two checker files were.
