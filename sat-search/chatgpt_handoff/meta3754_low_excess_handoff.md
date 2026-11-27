# L-meta-3754 — low-excess circuits (paper proof)

## Scope and verification

This is a new paper argument using checked one-junk and liveness/collector facts. It is not yet formalized in Lean. It neither claims nor assumes the general many-junk conjecture. The exclusive-cone Lean run 46045805869 at 27fb8a3a52c53c05bfb5dc30546fcdd59ad51114 was active when the argument was developed. Do not supersede it. The latest previously successful full check is dc4cb54579381408c53500c3a40575659f083f29, run 46044654103 (106 permitted axiom reports). The present documentation changes no Lean source or workflow. The independent tree-DP work addresses partial cared-row labels; this argument concerns the full edge function and does not modify that work.

## Result

For any simple graph, a least exact binary AND/OR circuit C at a lift fixed point, with positive gate count N and at most one unit of read excess, has at most one dirty AND. Here R is the number of DISTINCT raw inputs read by the circuit, and read excess is s=N+1-R. In particular, if v is the number of nonisolated vertices and N<=v, then s<=1, and hence the at-most-one-junk conclusion applies. For bipartite C4-free G, the already checked noLeastOneJunk excludes exactly one; thus every AND is below F. The zero-gate case is vacuous. The bound on s is meaningful because every essential raw input must be read; R>=v. We need not assume isolated inputs are absent.

## Checked ingredients and elementary counting

* outputLast: a nonempty least circuit has its last gate as output. allLive / noUnreadGate: every other gate has an output reader.
* everyGateHasLostEdge: false suspension of any single gate rejects at least one graph-edge minterm in a least circuit. The proof-tree consequence is that EVERY accepting proof tree on that edge contains an occurrence of that gate. Otherwise choosing the same OR branches and the same AND children proves acceptance after suspension.
* cleanReader / cleanWireReader: a clean gate is read only by clean ORs at a least lift-fixed point. The output gate is clean. Every accepting proof tree (select one true child at each OR, both at each AND) therefore has a first clean AND below the clean OR collector, and any dirty gate in it is strictly below that AND. A clean gate cannot be a raw input, since F is false on singletons. Equivalently use the proof of cleanHasTop.
* Any accepting proof tree on pairInput u v has all raw leaves labelled u or v. As a rooted tree with unary selected ORs and binary ANDs, its number of leaves is 1 + its number of AND occurrences. This identity does not require that the circuit be a formula.
* Count reads with multiplicity, even if a gate reads the same wire twice. There are exactly 2N reads, R distinct raw wires read, and N-1 distinct gate wires read (the output is last). Therefore
      s = N+1-R = sum_raw (reads-1) + sum_nonoutput_gate (reads-1),
  with every summand nonnegative. Thus s=0 means no wire is read more than once. If s=1, precisely one wire is read twice and all others once; it is either a raw input or a gate H. This is the full-cube analogue of the read-count identity in TREE_DP.md; the ensuing argument additionally uses exact edge minterms and checked clean-reader restrictions.

## Case s=0

The live circuit is a binary formula with distinct raw leaf labels. Every accepting proof tree on an edge has at most two leaves and at most one AND occurrence. If a dirty AND existed, select its pivotal edge by everyGateHasLostEdge. Any proof tree for that edge contains the dirty AND AND the first clean AND, distinct nodes, contradiction. Thus no junk.

## Case s=1, one repeated raw input a

The circuit is a binary formula in which exactly one raw label a occurs twice, and all other raw labels occur once. Take any dirty AND j and a pivotal edge. An accepting proof tree contains j and a clean AND, hence at least three leaves. Since there are only two active raw labels, it has at most three leaves, and must use both occurrences of a and one occurrence of the other endpoint. It has exactly two ANDs, of which precisely one is dirty. Let B be the fixed least common ancestor of the two occurrences of a in the full formula. B must be an AND (otherwise a selected OR branch cannot contain both occurrences). Every such proof tree contains B.

* If B is dirty, the unique dirty AND of every pivotal proof tree is B. Thus every dirty AND is B.
* If B is clean, B is the clean AND of every such proof tree. The only other AND is the dirty j, strictly in one of its two branches. Since that branch has two leaves in the proof, one is its occurrence of a; the other branch has only its occurrence of a. In particular j lies on the fixed path from B to the repeated occurrence in its own branch. There cannot be two dirty ANDs on one branch path: in a pivotal proof for the deeper one, all ancestors on this path are included, giving at least three ANDs including B. If there were one dirty AND in each branch, their respective pivotal proofs show that the opposite branch can be proved using its occurrence of a alone. Both children of B would then accept singleton a, making B true on that singleton, contrary to cleanliness. Thus at most one dirty AND.

This argument uses the fixed tree, not a choice of two unrelated duplicated leaves across different proof trees.

## Case s=1, one gate H read twice

The fan-in cone of H is a read-once formula on distinct raw inputs U. Every gate inside that cone other than H has exactly one read and no outgoing use outside the cone; similarly each input in U has only one read. Replace the cone by a placeholder leaf h at each of the two uses of H. The outer circuit is a formula with two h leaves and distinct raw leaves outside U, disjoint from U. There are no other duplications.

### H clean

All paths from H to the output are clean OR paths. An accepting proof tree that contains H chooses only one occurrence of H, and all gates outside that occurrence on its selected collector path are ORs. It contains no AND outside H's cone. The proof inside H is read-once with distinct raw labels. Any pivotal proof for a dirty AND in H's cone would contain a first clean AND inside the cone as well, requiring three distinct raw leaves on a two-vertex edge. A pivotal proof for a dirty AND outside the cone cannot select H (the H-to-output selected path is only ORs, so no other branch is included); it uses distinct raw labels and likewise cannot contain both a clean and dirty AND. Therefore no dirty AND in either region.

### H dirty

An accepting outer proof cannot have only h leaves and no outside raw leaf: such a proof would make the actual output true on every input on which H is true, contradicting that H is dirty. More explicitly, setting all outside-U variables false and H true would still make the outer formula true, so any negative input witnessing H's dirtiness would be accepted by monotonicity. Every selected use of H thus requires at least one outside raw leaf.

There is no AND in H's cone. If an AND there existed, take its pivotal edge and any accepting proof. The proof must contain that AND within an occurrence of H. As the H-cone is a distinct-leaf formula, its selected subtree containing the AND needs at least two distinct U vertices; an outside raw leaf is also necessary. This is impossible on an edge. This reasoning also excludes H itself being an AND. Hence H is a pure OR of its nonempty distinct raw support U. All dirty ANDs are outside it.

For any outer dirty AND j, select a pivotal edge and an accepting proof. No clean gate lies inside the H-cone (a clean gate in it would propagate through clean ORs to H). The outer proof therefore contains the dirty j and a distinct clean AND; it needs at least three outer leaves. If no h is used, raw labels are distinct and there are at most two leaves. If h is used, the edge has at least one active U vertex and at least one active outside vertex. Consequently only one outside vertex is available, and the only possible three outer leaves are the two h occurrences and that outside raw leaf. The outer proof has exactly two ANDs, one clean and one dirty, and must contain the fixed LCA B of the two h occurrences, an AND. The same LCA dichotomy as the repeated-raw case applies:
* If B dirty, it is the unique dirty AND in every pivotal proof, so at most one exists.
* If B clean, each dirty AND is on one of the two fixed branch paths to h. Two on one path would require three ANDs in the deeper pivotal proof. If one on each branch existed, the opposite branches in their respective pivotal proofs each accept h alone; B then accepts any actual input on which H is true. This contradicts B clean and H dirty.

This proves at most one dirty AND for all s<=1 cases. The sharing analysis is for a single twice-read gate, not arbitrary duplicated subtrees; do not generalize without new argument.

## Graph-specific consequence

Let m=|E(G)|, v=#nonisolated vertices, and tau the size of a minimum vertex cover (ignore isolated vertices). For a nonempty graph, choose such a cover and assign every edge to one of its covered endpoints. A nonempty assigned star with d edges costs d gates (d-1 ORs and one AND). The t nonempty stars cost m gates in total, and their collector costs t-1<=tau-1. This yields N<=m+tau-1 in any least circuit. All edge endpoints are essential since changing that vertex on the singleton of its neighbor changes F. Hence R>=v and the read-excess identity yields N>=v-1.

If m+tau<=v+1, then N<=v and s<=1. For bipartite C4-free graphs, at most one junk plus the checked noLeastOneJunk proves the entire clean conclusion in this class. In particular:
* a disjoint union of nonempty stars has m=v-components and tau=components;
* a forest with star components except at most one component having a vertex cover of size two satisfies m+tau<=v+1 (e.g. a double-star or four-vertex path).
The statement covers arbitrary least circuits, not just the explicit clean comparator. It is not a claim that every forest satisfies the numerical premise.

## Next

Formalize the low-excess theorem if useful: prove the read-count identity and a proof-tree certificate for a pivotal edge, then the unique repeated-leaf/LCA case analysis and single shared gate reduction. Prefer a native circuit proof-tree representation consistent with pinned ReadK definitions. Check the active global compiler run first; do not abandon the general exclusive-cone target. For s>=2 multiple repetitions can support different pivotal proof trees, so the unique-LCA proof does not settle the full conjecture. In particular a general minimal-counterexample reduction to low excess is still missing. No upstream PR.
