# Tight single-selector normal form and query-decoder tradeoff

Date: 2026-11-26. Starting master 2a476a4634bdd04817ef28644a6004912a61597f. Continues [binary selector elimination](binary_selector_elimination_handoff.md) and [restriction-stable ancestry and cascade rigidity](restriction_stable_ancestry_handoff.md). New paper classification of exact data-dependent B2 budget for a SINGLE selector, conditional total size tradeoff, and finite regression. No independent audit, Lean verification, production changes, priority claim or unrestricted superlinear SAT result. L-clb-036 remains open.

## 1. Model, premises and imported lemmas

A single output selects one of D>=3 independent data bits x_i. The allowed query domain Y is independent of the entire data cube. Every allowed q selects some i(q), and each i occurs. Arbitrary query-only preprocessing is allowed; it is uncharged in B_D, the number of original live proper binary gates with syntactic data ancestry. Signed wires, constants and fanout free. XOR/XNOR are counted proper binary gates, unlike in the XOR-AND model. Remove dead gates and simplify trivial aliases before counting. All results concern the live simplified graph, not padding with redundant dead gates.

Assume B_D=2D-1, equality in the previous selector lower bound. We use the following proved-on-paper results of the earlier handoffs (not separately formalized):
- single-bit deletion retaining at least two entries leaves a selector needing 2(D-1)-1 data-dependent gates; hence at most two counted gate removals;
- every data bit has one or two direct readers; two readers must both be parity gates; a sole reader is canalizing, has exactly one successor, and its other operand is query-only or a branching counted gate. These are Section 4 of restriction_stable_ancestry_handoff.md. The sole-parity exclusion uses reassociation and the impossibility of a sole reader dominating another selectable bit;
- forcing k pairwise ancestor-incomparable live gate outputs constant, while the required output remains nonconstant, collapses at least k additional original gates, by the constant-seed wire-count lemma.

All the below proofs use gate IDs, not translation rank. No assertion about D=2 in the rigidity theorem: the XOR-based three-gate mux is a counterexample to sole-reader canalizing necessity in that case.

## 2. No saturated branch in a tight single selector

For a branching counted gate v define X_v to be the data bits whose sole readers use v as their other operand. Call v saturated if every outgoing edge goes to one of these readers. Their IDs are distinct: a sole reader cannot read two data bits (prior rigidity). The set X_v has cardinality k=outdegree(v)>=2. Its readers are pairwise ancestor-incomparable, since their only operands are v and distinct primaries. Also v has no ancestry from any X_v bit: each such bit appears only at its reader, a strict descendant of v.

Suppose v saturated. Since v is counted it has a data ancestor outside X_v, so k<=D-1. Force all X_v bits to the respective controlling values of their canalizing readers and retain queries selecting only the other bits. All k readers become constants. By the cascade lemma at least k additional counted gates collapse downstream; all these gates are data-dependent in the original graph. Moreover v becomes dead because all its successors have been removed, giving one further distinct original gate removal. Hence at least 2k+1 of the original 2D-1 counted IDs disappear. If k<=D-2 the remaining selector needs 2(D-k)-1 counted gates; at most 2(D-k)-2 remain, contradiction.

It remains to rule out k=D-1. Write z for the sole outside data bit. The retained target is z, nonconstant, even though it needs zero binary gates. The same cascade removes at least 2k+1=2D-1 counted gates, exhausting the entire original counted budget. All k seeds, k downstream collapses and v are distinct, and none of these except v is an ancestor of v. Thus v cannot have a counted proper gate ancestor. Since v has data ancestry only from z, it must read z directly and a query-only signal (the other operand cannot be another raw data or z again in a proper simplified gate).

There must be another direct reader of z: otherwise every path from z to output goes through v and then one of its saturated successor readers; forcing those readers constant would make the retained output independent of z, contradiction. Thus z is twice-read, and by earlier rigidity its reader v is XOR/XNOR up to phases. At every fixed query the value v varies with z. Choose any allowed query selecting x_i in X_v. Its sole reader g_i is canalizing in the side operand v, so one of the two values of v makes g_i independent of x_i. Choose z to attain that value (v does not read x_i); then the whole output cannot depend on x_i, contradiction to selection of x_i for EVERY data assignment. Therefore no saturated counted branching vertex exists.

Important: this last argument uses the single-table fact that all X_v bits can be removed while keeping a nonconstant one-bit target. It does not directly handle a saturated branch capturing an entire table of a batched AND product, because fixing all of that table to controlling constants might annihilate the required product. No closure of the batched r-1 gap claimed.

## 3. Slot equality and exclusion of twice-read data

Let b be number of twice-read data bits, Q the number of operand occurrences in counted gates whose source is query-only (including raw query primaries), e=sum(outdeg(v)-1) over nonoutput counted gates. Counted gates are all live; since any descendant on an output path is counted, each nonoutput counted gate has at least one counted successor. The counted output has none. Proper gates have two operand slots. Count direct data occurrences D+b, internal counted edges B_D-1+e, query-only occurrences Q. Thus
    B_D=D-1+b+Q+e.
At tight budget this gives D-b=Q+e.

There are D-b distinct sole-reader gates, one for each once-read bit. Their side operand is either query-only or a branching counted gate. For each counted nonoutput v, since v is not saturated, the number of its outgoing occurrences feeding those sole-reader side slots is at most outdeg(v)-1. Hence
    D-b <= Q+e.
Equality is forced by the slot equation. In particular every query-only operand occurrence must enter a sole-reader gate as its side operand: otherwise the inequality would be strict (the side-slot count from counted sources is at most e). Also every counted nonoutput gate spends exactly outdeg(v)-1 outgoing edges on these side slots. No assertion that each of the Q query signals is distinct yet.

If b>0, set every once-read data bit to its own controlling value. All sole-reader outputs become fixed constants independent of query, including those with counted side inputs. Every query-only entry into the counted subgraph goes to one such reader; with those outputs fixed, the entire output is independent of query as a function of the remaining twice-read bits. But choose a query selecting a twice-read bit. The residual is exactly that independent bit. If another twice-read bit exists, a query selecting it is a different residual. If only one twice-read bit exists, choose any once-read bit (D>=3); selecting it gives a constant residual. In either case contradiction. Therefore b=0 and every data bit is once-read.

Now suppose some sole reader g_i has a counted side operand v rather than a query-only one. Fix all other data bits to their controlling values, leaving x_i free. All their readers become constants. All query-only entry slots are in those other readers, since g_i has counted side input. Again the entire residual is independent of query, while selecting i gives x_i and selecting any other bit gives a constant. Contradiction. Thus every data reader has a query-only side operand.

Consequently Q=D, and e=0 by the slot identity with b=0. All counted gates except output have outdegree exactly one. The D distinct sole-reader gates each read one data primary and one query-only signal; every other counted gate reads two counted gate signals. The counted graph is a read-once rooted binary merging tree with these D reader gates as leaves and D-1 internal merge gates. This proves the topological normal form, not merely existence of a circuit in that form.

## 4. Exact Boolean normal form on the allowed domain

Write c_i for the controlling data input value of sole reader g_i, and d_i for its resulting constant output. These are raw actual bits, with phases absorbed into the proper binary truth table. Each g_i is canalizing in its side signal as well; let e_i(q) in {0,1} be the indicator that its side signal has the noncontrolling value. Direct truth-table inspection of signed AND/OR gives
    g_i(x_i,q)=d_i + e_i(q)*(x_i+c_i)   [GF(2)].
The two additions are XOR; this is an algebraic characterization, not extra free gates in the B2 model.

Set all x_i=c_i. All reader outputs are d_i, hence final output constant independent of q. But selecting each i returns c_i, so ALL c_i are the same c. With all leaves fixed at their baseline d_i, every internal merge has a well-defined baseline value. At a query selecting i, flipping only x_i from c must flip the final output. Therefore its reader is enabled, e_i(q)=1, and the unique path from its leaf to output is sensitive to a flip at every merge when the other child is at its baseline. These baseline values are query-independent. For any query not selecting i, the same data variation must NOT flip output. Since the path sensitivity at baseline is fixed, this forces e_i(q)=0. Thus
    e_i(q)=1 iff i(q)=i.
This proof allows multiple query assignments selecting the same bit; it does not require all possible query-port assignments to be allowed.

Every internal merge has two nonempty leaf subtrees. For each child choose one selectable leaf in that subtree. Flipping it at its selecting query must propagate through the merge. Thus when expressed in child/output deviation bits from their baselines, the merge truth table has values 0,1,1,z on input pairs 00,01,10,11, with z any bit. These are exactly XOR and OR. No assertion that OR and XOR are interchangeable outside the allowed domain: since exactly one reader is enabled, at most one leaf has a nonzero deviation on the actual domain, and either merge computes the same union of active deviations there.

Conversely any one-hot decoder (possibly arbitrary/free), D signed reader gates of the displayed form with common c, and any binary tree of signed OR/XOR deviation merges with output baseline c, realizes the selector. Hence the classification is necessary and sufficient at tight data budget, up to phase choices, tree shape and arbitrary query-only preprocessing. The decoder signals are pairwise distinct even modulo complement when D>=3 (each enable selects a different nonempty query class, and a third nonempty class excludes complement equality).

## 5. Conditional total gate lower bound for binary addresses

For D=M=2^k, k>=2, assume exactly k independent address bits, each address selects its own bit. At tight data count 2M-1 the above theorem forces every one of the M query-only enable sources to compute an address minterm, up to a sign. These M minterms are pairwise distinct modulo complement, and none is a constant or signed query primary for k>=2. Therefore at least M distinct query-only binary gate IDs are required. The earliest gate computing any minterm in a topological order depends essentially on all k query bits. Its query-only input cone needs at least k-1 binary gates by the ordinary live-cone leaf count. None of its strict gate ancestors can compute a minterm up to sign (earliest choice). Thus there are at least k-2 additional distinct query-only gates, disjoint from the M enable-source IDs. This proves
    B_Q >= M+k-2,
    B_total >= (2M-1)+(M+k-2)=3M+k-3, CONDITIONAL on B_D=2M-1.
The total includes original live proper binary IDs, with signed wires and constants free. Here B_Q counts query-only gates in the simplified restricted circuit, not necessarily query-only gates in an unrestricted original SAT circuit.

The ordinary binary mux tree gives total 3(M-1)=3M-3 with no query-only gate preprocessing (three counted gates per two-way mux). Consequently no total-size-minimizing ordinary binary circuit for k>=2 can have minimum possible data-dependent count: any such circuit must have B_D>=2M. This is a genuine resource tradeoff, not a lower bound 3M+k-3 for ALL circuits. We do not assert 3M-3 is the exact unrestricted total complexity. Unconditionally B_total>=2M follows from the dichotomy B_D>2M-1 or equality plus the decoder cost; this is only one more than the old unconditioned data lower bound. No stronger universal numerical claim. The result illustrates why minimizing only one gate class can hurt overall synthesis.

Examples:
 k=2,M=4: minimum data count 7, conditional query lower 4, conditional total >=11, mux upper9.
 k=3,M=8: minimum data count15, conditional query lower9, total>=24, mux upper21.
 k=8,M=256: minimum data count511, conditional query lower262, total>=773, mux upper765.
No claim of exact decoder complexity for k>2; earliest-minterm count is only a lower bound.

Transfer: the previously verified r_group=1 packed lookup grammar in packed_directional_handoff.md has exactly k independent query polarity bits and M single-copy table bits, all other physical inputs fixed. Apply the theorem to the actual simplified B2 circuit after this legal restriction. If its data-dependent count is 2M-1, its remaining query-only gate count obeys the conditional lower bound above. If the ORIGINAL unrestricted SAT DAG has exactly 2M-1 binary gates with designated table ancestry, then the restricted simplified count is <= that and >=2M-1, hence equality, so the original total count is also >=3M+k-3. Otherwise no such conditional count is inferred. Restriction cannot introduce IDs or new ancestry. No new physical grammar/padding replay, no claim of improvement over strongest repository-wide SAT bound, and no superlinear claim.

## 6. Executed regression

Run node tight_selector_normal_form_check.js. Checker body executed in JavaScript tool runtime before upload, not independently in Node or Lean. Seed 870049.
- 64 saturated-branch local controls, covering parity v and every canalizing reader truth table, both operand orders and both fixed query input values; each has a choice of the outside data bit disabling the reader.
- Complete 51,200 truth-table assignments to the specified three-leaf reader/merge tree: 8 proper canalizing reader choices per leaf, 10 proper merge choices per internal node. Exhaust all independently assignable query-port settings; accept only if every data projection occurs. 1,024 valid assignments, with 3,072 projection contexts; 512 common control phase0, 512 phase1. Each satisfies exact one-hot and signed OR/XOR classification.
- 1,800 sampled four-leaf trees (5 valid); 600 planted signed one-hot trees of three/four leaves and 2,400 local truth-table mutations (570 valid mutants). All valid cases satisfy normal form.
- Binary address decoder checks k=2..10, exact minterm distinction modulo complement, exclusion of primary literals, and essentiality of every address bit (18,432 essentiality comparisons). All passed.
These are regressions of the local saturated obstruction and truth-table/decoder classification, NOT exhaustive enumeration of arbitrary reconvergent tight circuits. Their exclusion follows from the paper argument in Sections 2--3. Checker commit 16f83aabdfed9f6e2ee3197f5ebf7c4c7a28325f.

## 7. Next steps and limitations

The single-table equality structure is now completely characterized at the paper-proof level, conditional on the earlier rigidity lemmas. This gives a strong topology and truth-table pruning rule for certified selector restrictions at exactly minimum data budget, but no general claim for arbitrary partial functions or for AIG engines with a different cost model. AIG is a subset of B2, so necessary conditions transfer, but the three-gate mux upper construction and one-hot gates must be interpreted with signed wires. No production integration or performance benchmark done.

The original goal of this round was to attack saturated branches for batched lookup. The single-selector case is closed; the difficult entire-group case remains. Do not sum the conditional decoder cost with other restrictions' charges. The next useful direction is generalize the query-dependence loss argument to a saturated branch that captures one whole group while retaining other groups, or derive a slack-dependent structural theorem when B_D exceeds 2D-1. More importantly, lookup targets have linear upper constructions, so even their complete classification cannot prove L-clb-036. Keep this as a structural testbed for harder SAT restrictions. Independent audit and Lean formalization remain outstanding. No production changes or upstream submission.
