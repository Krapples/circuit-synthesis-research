# Closing the two-table data-dependent binary-gate gap

Date: 2026-11-26. Starting master 0ddddd0dd64069dc6ab4adee5327f341c16819ad. Extends [binary selector elimination](binary_selector_elimination_handoff.md), [restriction-stable ancestry and cascade rigidity](restriction_stable_ancestry_handoff.md), and [tight single-selector normal form](tight_selector_normal_form_handoff.md). New paper exact B2 data-dependent complexity for two independently addressed tables, stronger lower bound for any number of tables, improved subset ancestry constraints. No independent audit, Lean verification, production changes, priority claim, new physical grammar or unrestricted superlinear lower bound. L-clb-036 remains open.

## 1. Setting and prior lemmas

Count ordinary proper binary Boolean gates (B2: all ten functions essentially dependent on both inputs), with signed wires/NOT, constants and fanout free. Work in the live simplified output cone. XOR/XNOR count as binary gates here, NOT the free-affine XOR-AND multiplicative-complexity model. Query-only preprocessing may be arbitrary and is uncharged. B_D counts gates with syntactic data ancestry in the resulting restricted circuit. All data bits independently free, allowed query domain independent of them.

There are r>=2 groups of sizes M_j>=2, D=sum M_j. The target F=AND_j H_j[q_j] has all independent address choices. The previous elimination theorem gives B_D>=2D-r; any removal of a table entry when at least one remains in that table deletes at least two distinct original data-dependent gate IDs, preserving all other data assignments and the allowed queries avoiding that entry. The prior equality-budget rigidity theorem applies when B_D=2D-r and all original groups have size >=2:
- Each data bit has one or two direct readers. Twice-read bits have only parity readers. A sole reader is canalizing, has exactly one successor, and reads either a query-only signal or a branching counted gate as its other operand. No two sole-reader bits share their reader.
- With b_2 twice-read bits, Q query-only operand occurrences entering counted gates, and e=sum(outdegree(v)-1) over nonoutput counted gates, the slot identity is B_D=D-1+b_2+Q+e.
- A counted branching vertex is saturated if all its outgoing wires go to side-input slots of sole-reader gates. For a tight batched circuit, at least r-1 saturated branching vertices are required. In particular e>=r-1. This follows by charging each of D-b_2 sole-reader side-input occurrences either to a query-only occurrence or to a counted outgoing edge; an unsaturated vertex can contribute at most its outdegree-minus-one, whereas a saturated vertex can contribute one more. Thus D-b_2<=Q+e+|H| where H is the saturated set. Combine with slot equality.
All of these are prior paper results, not independent formal verification. The present proof depends on these lemmas, particularly the equality-budget reader rigidity. The new conclusion does not require any translation-rank results.

## 2. Reduce to two entries per group

Assume a hypothetical equality-budget realization with B_D=2D-r. Delete M_j-2 entries from each group by the previous two-gate elimination rule, retaining all independent choices among two entries per group. The remaining data count is 2r, and at most (2D-r)-2(D-2r)=3r data-dependent binary gates survive. The previous lower bound on this restricted target is exactly 3r, so it must attain equality.

The reduction may use parity-reader substitutions depending on remaining inputs; it does not insert any new circuit gates because the sole reader is replaced by a constant. The resulting simplified counted DAG has original IDs with no new original data ancestry. The restricted query domain may be arbitrary (e.g. two allowed address codes per group); no requirement that a chosen pair be a coordinate subcube.

## 3. Query-port counting excludes equality for r>=3

The output of the data-dependent cone is a deterministic function of the 2r free data bits and the Q query-only operand values. Repeated occurrences or complementary wires do not increase its number of possible query residuals beyond 2^Q. In particular every distinct target residual must correspond to a distinct Q-bit vector (not necessarily a unique vector; there may be many realizations of a residual).

There are exactly 2^r distinct products, one for each choice of an entry in each group. Distinction follows by setting the chosen bits of one product all to 1 and setting a bit chosen only by the other product to 0. Thus Q>=r. The slot identity at D=2r,B_D=3r reads
    b_2+Q+e=r+1.
But previous saturated-branch theorem gives e>=r-1. If r>=3 then Q+e>=2r-1>r+1, contradiction. Therefore no circuit with B_D=2D-r exists for r>=3 (nor with a smaller budget by the prior lower bound). This is a proof for arbitrary group sizes >=2 by Section 2, not only for equal sizes.

The same query-residual bound at arbitrary budget is Q>=ceil(log2 product_j M_j). The slot identity used at tight budget assumes at most two direct readers per data bit. At general budget replace b_2 by total excess direct-data occurrences sum_i(readers_i-1). The counting identity remains valid if proper simplified gates have distinct operands. It is not by itself a bound on internal fanout away from equality.

## 4. Two groups: the unique tight six-gate shape is impossible

For r=2, D=4, B_D=6, the identity and inequalities force
    b_2=0, Q=2, e=1.
There are four distinct sole-reader gates, all canalizing and each with exactly one successor. The remaining two counted gates consist of the output and a unique branching vertex v of outdegree two, since e=1. The prior theorem requires a saturated vertex, so v is saturated. Exactly two of the four readers read v as their side input, and the remaining two must read query-only signals because v has no other outgoing wires and there is no other branching counted source. Both query occurrences are therefore consumed. The gate v cannot read a raw data primary: all primaries already have their sole readers, and v itself is not a reader (outdegree two). It cannot read query-only operands because both slots of that type have already been consumed. It must read two distinct counted gates; the two readers fed by v are descendants and cannot be its inputs, nor can the output be an input. Hence v reads precisely the other two readers. Each of the two readers fed by v has only the output as possible successor: neither can feed the other because that other reads its own raw bit and v; neither can feed an ancestor. The output thus combines those two readers.

This completely determines the unsigned counted topology up to label/order changes. Signed phases can be absorbed in the proper truth tables. The downstream part computes a fixed function h(u,w,v) of the two raw data bits u,w whose sole readers are fed by v, and one common bit v. Everything upstream of v depends only on the other two data bits and query. In particular v is independent of u,w, so as upstream data and queries vary, the output residual on (u,w) can take at most two distinct Boolean functions, namely h(u,w,0) and h(u,w,1). This argument is even valid for arbitrary upstream functions and arbitrary downstream h, not merely the allowed two-gate truth tables.

But the target needs more than two distinct such residuals:
- If u,w belong to the same table, set both entries of the other table to one. Its two selectable entries give residuals u and w. Set both entries of the other table to zero to get the zero residual. These three functions are distinct.
- If u,w belong to different tables, set the other entry of each table to one. Independent choices of addresses give residuals 1,u,w,uw, four distinct functions (zero is also possible by other fixed outside data). All retained choices are legal.
Contradiction in both cases. Thus 6 data-dependent gates are impossible. The 7-gate upper construction is two ordinary 2-way muxes (three binary gates each, using free signed select wires) and one AND.

Notice the same-table argument changes the outside DATA assignments as well as the query. The one-bit interface bounds the number of residuals across both, because the downstream part has no other external input. Using only the two address residuals with outside data fixed to one would NOT give a contradiction.

## 5. Main numerical results and simultaneous ancestry bounds

For every r>=2 and every group size M_j>=2:
    B_D >= 2D-r+1.
For r=2, this is exact:
    B_D = 2D-1 = 2(M_1+M_2)-1.
Upper: one query-only one-hot decoder per table, M_j proper AND gates gating its data bits and M_j-1 OR gates combining them, then r-1 AND gates combining table results. Total counted gates 2D-1; query-only decoders arbitrary and uncharged. This also gives general upper bound 2D-1 for r>=3, so remaining gap at most r-2 rather than r-1. Do NOT claim exact total gate complexity with binary addresses; query-only decoding gates may cost more. This is not multiplicative complexity.

For equal sizes M power of two, two-group B_D=4M-1, previously 4M-2. Examples: M=2,4,8,256 give 7,15,31,1023. For r=3, lower 6M-2 and upper 6M-1. For fixed r the numerical improvement is one gate, not a new asymptotic growth rate. It is a genuine unconditional improvement within this model, unlike a necessary condition only at hypothetical equality.

**Stronger subset bounds:** In an original batched selector DAG let S be any data subset and f(S) the number of complete original groups contained in S, all original groups size>=2. Let A(S) be the union of original live binary gate IDs descended from S. Then
    |A(S)| >= 2|S| - f(S) + 1_{f(S)>=2}.
For f=0 or 1 this is the old theorem. For f>=2, fix all outside-S data to 1, then remove all S entries in partial groups, choosing bypass addresses outside S. Each such deletion removes at least two original distinct IDs descended from the erased bit; at each stage the full groups remain, so retained target still depends on other data. The remaining f complete original groups compute the same f-group product with independent addresses. Their counted gates require at least 2D_full-f+1 by the new theorem; all their surviving original IDs have S ancestry, are distinct from all removed IDs, and restriction cannot introduce new ancestry. Summing these DISJOINT charges proves the subset bound. The same proof works for f=1 with old selector count and for f=0 with the old deletion sequence. These are simultaneous necessary constraints on one graph. They do not imply a universally preassigned extra matching demand on any specified input or group: subsets containing only that group may still have the old bound. No addition across unrelated restrictions.

## 6. Transfer to the original packed SAT grammar

Reuse precisely [packed_directional_handoff.md](packed_directional_handoff.md), Section 4: independent groups, M=2^k, k free address polarity coordinates per group, all table data bits occur exactly once at fixed physical positions, remaining grammar bits fixed. The target after restriction is the product of independent lookups, with length Theta(rM) when r<=M^c as previously proved. For r>=2 the original SAT binary gate DAG must have at least 2rM-r+1 original live gates with ancestry in those data positions; for r=2 the restricted data-dependent lower bound is 4M-1. The upper construction establishes exact complexity of the ABSTRACT lookup target with free query-only preprocessing, not exact SAT size, or even exact total lookup size in B2 or AIG. Restricting physical primaries cannot add original gates or original ancestry. No new encoding or padding verification performed. This may not improve the repository's strongest total SAT lower bound at a given length. Because the restricted target has a linear data-dependent and linear/quasilinear total upper construction, this does not establish L-clb-036.

## 7. Executed regression

[batched_selector_tight_gap_check.js](batched_selector_tight_gap_check.js), commit b1621050eb2943dc57e8cb3ca2a4e60591337b76. Executed checker body in JavaScript tool runtime before upload, not separately Node, native C++ or Lean.
- Enumerate all 8^4*10^2=409600 truth-table assignments to the forced six-gate shape (four canalizing readers, two arbitrary proper binary merge/branch gates). Absorb signed wire phases into truth tables. Evaluate all four independent settings of its two query-only ports, 1,638,400 contexts, each a bitset of the complete 16-row data truth table. In each of the two possible group layouts (same-group or cross-group saturated pair), check whether every one of the four target residuals occurs somewhere. No assignment realizes all four. Maximum target residuals available across query settings: 2 in same-group layout, 1 in cross-group layout. These maxima are specific to the forced topology, not a theorem for all circuits with six gates independent of the prior structural reduction.
- Enumerate integer slot conditions b_2+Q+e=r+1, Q>=r, e>=|H|>=r-1 for r=2..24; exactly one possibility for r=2 and none for r>=3. General impossibility follows algebraically for all r.
- Explicitly compute downstream residual sets across all outside data assignments and query choices on each grouping, 128 bit evaluations. Same-group residual set {0,u,w}; cross-group {0,1,u,w,uw}. Both exceed two.
- Validate seven-gate upper on all 64 assignments to four data and two address bits.
All assertions passed. Enumeration of the forced shape is not exhaustive unrestricted synthesis; the general proof is the structural reduction plus one-bit interface obstruction. No independent proof audit or formal Lean proof yet.

## 8. Scope and next research step

The prior equality-budget obstruction is now resolved for all r>=2, and the two-table gap is closed. The general r>=3 exact B_D problem remains open here; next investigate slack-budget structural constraints (e.g. three-table gap of one), but do not devote disproportionate effort to these linear-size targets. The decisive next advance toward L-clb-036 must involve a harder SAT family or a cross-restriction structural charge that cannot be saturated by the individual linear lookup circuits. No production algorithm modifications, external submission, or claim of novelty relative to classical selector/gate-elimination literature. Independent audit of prior tight-reader lemma and new proof remains outstanding.
