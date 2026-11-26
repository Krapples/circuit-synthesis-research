# Feedback compatibility and structural history separators

Date 2026-11-26. Base [e67385e](https://github.com/Krapples/circuit-synthesis-research/commit/e67385efdb039b579611901d2f30e8ed2c88d38c). Extends [causal_response_handoff.md](causal_response_handoff.md). This round establishes the suggested partial-response compatibility coloring theorem, a noncircular topology-only upper capacity using upstream feedback separators, a strict separation from ALL prior causal cut inequalities on explicit candidate lookup topologies, and preservation of the additive gate charge with fractional capacities. No new unrestricted superlinear size bound, Lean theorem, production solver changes or literature-priority claim. L-clb-036 remains open.

## 1. Setup and scope

Use the previous partition A,B of the original directed circuit graph, with output in B, varying A data primaries S, other A inputs fixed publicly, and a common allowed domain Y of B inputs independent of the data assignment x. The domain may contain only legal metadata contexts. Let X={0,1}^S. For each vertex v in A, D(v) is its local A-only data support and R(v) its local reverse-port ancestor set, as defined previously. The original causal capacity is

    c_old(v)=min(|D(v)|,2^|R(v)|).

When reverse-port values are treated as independent formal parameters, the local response T_v(x,h) is a Boolean function of h on R(v), with dependence on x only through D(v). In actual full-circuit evaluation on (x,y), write H_v(x,y) for the vector of values of R(v), and V_v(x,y) for the value of v. Then V_v(x,y)=T_v(x,H_v(x,y)). Every component of H_v is topologically earlier than v.

Define the partial response P_v(x) on histories h that occur for some y in Y at this fixed x; P_v(x)(h)=V_v(x,y). This is well-defined by the formal response identity. Define the common history universe

    H_v = union_(x in X) {H_v(x,y): y in Y}.

This is a union across ALL data and allowed Bob inputs, not a domain chosen separately by the encoder for each row. Realizable histories may depend on the data and on previous forward messages.

## 2. Compatibility coloring theorem

Define a finite undirected conflict graph G_v with vertices x in X. Two data assignments are adjacent iff their partial responses disagree at some history in both domains:

    x ~_v x' iff exists h in dom(P_v(x)) intersect dom(P_v(x'))
                with P_v(x)(h) != P_v(x')(h).

Let chi_v be its chromatic number (one for an edgeless nonempty graph). A proper color class consists of pairwise compatible partial functions. Their union is a well-defined partial Boolean function; extend it arbitrarily to all formal histories. Thus each color has a fixed decoder that returns the required value at every actually reachable history for any row of that color. Conversely any common total-response decoder serving a set of rows makes that set independent. Hence chi_v is EXACTLY the minimum number of total history-only response decoders covering all rows. This exact interpretation does not claim optimality when the decoder is additionally allowed to use y, other cut codes, or earlier transcript values not in R(v).

**Theorem.** For any A-only vertex cut K intercepting every local path from S to the forward ports F, let N be the number of distinct output residuals on Y. Then

    log_2 N <= sum_(v in K) log_2 chi_v.

Encode the data row by one proper color at each cut vertex. Simulate the original circuit as in the earlier response-cut proof. At each v in K use its color decoder on the actual earlier reverse-port values. To avoid a circular use of actual histories, induct on the topological evaluation of B vertices and A vertices needed to produce forward ports. Every reverse ancestor of a cut vertex being evaluated precedes it. Its B value has already been correctly reconstructed. Hence the supplied history is the history that REALLY occurs for the original x,y, so the decoder is defined and correct. For an A forward port, any path to an unfixed data primary must encounter K; replacing cut values blocks the dummy data. All B gates, including the output, consequently evaluate correctly. Equivalently, evaluate the complete original DAG with dummy A data and override every K vertex using its color decoder; induction shows all B vertices are correct and therefore every override receives its true earlier reverse history. No assumption that feedback is independent of x or simultaneously attainable is made. Equal code vectors imply equal residual functions, and there are at most product chi_v codes.

In particular we have the hierarchy

    log_2 chi_v <= min(|D(v)|, |H_v|)
                    <= min(|D(v)|,2^|R(v)|)=c_old(v).

For the first bound, equal restrictions of x to D(v) imply identical formal response and therefore compatible partial responses; color by x restricted to D(v). Alternatively extend each partial response to a total table on the COMMON history universe H_v; at most 2^|H_v| distinct completions suffice. Both are valid even though the reachable domain varies across rows.

This improves the previous invariant semantically, but computing chi_v can require exponentially many data rows and actual circuit semantics. It is not yet a noncircular lower bound on unknown circuit size. It is a useful exact local compression oracle, or an upper-bound target for structural arguments. In particular do not substitute a LOWER bound on chi_v for an upper capacity when deriving a necessary cut inequality.

## 3. Noncircular structural refinement: feedback history separators

Let U contain all varying physical primaries on both sides (including the metadata and query bits allowed to vary). Let w(v) be the minimum number of original vertices meeting every directed U-to-R(v) path in the FULL DAG. Endpoints may be in the separator, and zero-length paths count. R(v) itself is an allowed separator, hence w(v)<=|R(v)|. With R(v) empty put w(v)=0.

Any such separating set Z has the property that the actual vector of values at R(v) is a deterministic function of the bits at Z and the public fixed primaries. This is simply the usual DAG cut reconstruction: compute R(v) recursively, stopping at Z, and no unfixed source can be reached without hitting Z. Even if Z contains A data or earlier feedback-dependent vertices, its values are just a |Z|-bit tuple. Thus the COMMON history universe obeys

    |H_v| <= 2^w(v).

Consequently a completely topology-based capacity is

    c_struct(v)=min(|D(v)|,2^w(v)) <= c_old(v).

It needs only the original graph, placement of primaries and known fixed inputs, not any truth table, exact chromatic number, or particular gate functions. It can be computed by unit vertex-capacity max-flow/min-cut in the full DAG with source set U and sink set R(v). Overapproximating U by all physical primaries remains sound. This is distinct from taking the old local feedback count: many distinct reverse-port gates may be generated from a much smaller shared upstream interface. More broadly any independently certified upper bound on the COMMON history count gives a valid capacity. A valid bound on history support need not assume fixed B-side feedback cones independent of data.

### Strict topology separation from all previous causal cuts

For k>=4 let M=2^k. Use the standard signed AIG mux tree with M data bits on A and k levels of address selection, all mux gates on A. At each level j, replace the normal address bit by a distinct B-side signal Q_j generated from only t=ceil(log2(k+1)) seed query primaries. For example take the first k nonempty subset ANDs of those t bits; their output vertices are distinct, with singleton subsets represented by the primary itself. For larger k there are at least k nonempty subsets. (The precise Boolean functions need not be conjunctions for the graph obstruction.) Put the remaining k-t query primaries on B and combine them with the final mux output by a B-side XOR chain. The final mux output is the sole A forward port. Every primary has a syntactic path to the output.

In the old capacity model there is a full flow of M units from the data to that port, so EVERY old internal causal cut has capacity at least M. Explicitly at mux level j (counting from 0) each of its two input branches carries 2^j original data sources, has at least j distinct feedback ancestors after j mux levels, and passes through one signed AND using Q_j; that AND has data support 2^j and j+1 reverse ancestors, so capacity 2^j. The complemented AND joining the two branches has data support 2^(j+1) and j+1 reverse ancestors, so capacity 2^(j+1). Each data source sends one virtual unit along this unique branch path to the sole port. At the final port the old capacity is M, and every prior vertex's capacity suffices. This argument is syntactic and permits shared B query logic. Consequently the earlier global strategy and direction tests also pass (a=1, b=k, total k+1, a*2^b=M; richness bound trivial). Yet the t seed primaries cut all free-primary-to-R(final port) paths in the full graph, and the new structural port capacity is at most 2^t < M for k>=4. INDEX has M independent residual bits, so the proposed graph cannot compute INDEX under any assignment of binary gate functions to its vertices. The explicit mux/AND/XOR AIG is a realization of the rejected topology, NOT a correct INDEX circuit.

At k=7, for example, 128 residual bits are required; all old cuts have capacity at least 128, but the structural port bound is eight. This rejects more topology than even optimizing the previous internal-cut bound over all K. It does not establish that every small graph for SAT has such a feedback separator. A correct ordinary mux tree with genuinely independent address sources does not have this bottleneck.

## 4. Fractional gate charge survives

The previous proof used integral vertex capacities. The coloring capacities c_col(v)=log_2 chi_v can be real, and no rounding to integers is required in the injective case. Choose any certified real upper capacities c(v) >= log_2 chi_v (such as c_struct, c_old, or a mixture independently justified at each vertex). All cuts have summed capacity at least log_2 N. The vertex-split directed network therefore has a real max flow of value at least log_2 N. In the injective case log_2 N=|S|, each data primary has capacity one (its partial history is the empty tuple and the two bit values conflict), and the maximum flow equals |S|. Each source supplies exactly one unit, possibly split over paths. Decompose the flow into weighted directed paths; the DAG is acyclic and the weights are nonnegative. Give each positive-capacity A gate cost 1/c(v), zero cost to primaries. The total weight paid at any actual gate is its flow load divided by c(v), at most one. If d_i is the shortest such path cost from source i to F, then

    s_A >= sum_i d_i.

The proof remains valid for real capacities and fractional flow, not only one integral path per source. Removing zero-capacity vertices is legitimate for flow paths. Decreasing any valid capacity increases path costs or removes paths, so the resulting metric bound never weakens for the same fixed partition and data set. No theorem here forces a superlinear metric sum. If N is not injective, real flow need not choose whole source units; use a fractional source-cost lower bound, not ceil(log N) integral paths. This distinction matters for noninteger capacities.

## 5. A counterexample to the naive per-row history count

It is tempting to use max_x |dom(P_v(x))| instead of the COMMON union size |H_v|. The bound on history-only code capacity log_2 chi_v is false with that substitution.

Take t>=17 possible histories indexed by [t]. Include a data row for every pair i<j and every possible ordered pair of Boolean values (a,b). Its partial response has exactly two entries, P(i)=a and P(j)=b. If four or fewer total decoders cover all these partial responses, form the signature of each history across these at-most-four decoders. There are at most 16 different signatures, so some two histories share a signature. None of the decoders can realize an unequal assignment to that pair, contradicting coverage. Thus chi>=ceil(log_2 t)>4 for t=17 (the lower bound is on the NUMBER of colors, not its logarithm). Therefore log_2 chi>2 even though every individual row has only two reachable histories. More generally the required number of completions grows at least log t. This is the standard binary covering-array observation, proved here directly.

This partial-response family is realizable in an ordinary acyclic communication/circuit setup: A holds i,j,a,b and sends i,j to B; Bob has an address y and sends back h=j when y=j, otherwise h=i; A computes v=a if h=i and b if h=j (i!=j). For every valid data row exactly the two histories occur, and every binary pair assignment occurs. All invalid rows can be assigned any deterministic defaults to obtain a total Boolean circuit, without reducing the required colors for the valid rows. This construction does not refute a more general joint decoder that also uses the earlier i,j messages or Bob's input; those may allow cheaper encodings. It refutes the particular per-vertex history-only estimate, not every possible improved causal cut inequality. It warns that data-dependent reachability cannot be treated as a common smaller table domain for free. The finite regression constructs the partial table family and checks the pigeonhole premises; no explicit AIG of this covering-array gadget was synthesized.

## 6. Executed regression

Run from this directory:

    node feedback_compatibility_check.js

Seed 870024. 379 retained circuits from 400 random AIG attempts and 40 explicit small mux attempts (retained cases have data and query primaries and <=4 data primaries for exact coloring). 1,921 A-side vertices: enumerate actual histories over all data/query inputs, build conflict graphs and compute exact chromatic numbers with exhaustive DSATUR-style search; verify merged color-decoder consistency and the complete capacity hierarchy. 167 vertices have color capacity strictly below old causal capacity, 166 strictly below common-history capacity. One strict common-history refinement and no strict topology-only refinements in the random/mux sample. 1,739 internal cuts; 51,784 direct reconstructions from cut color codes, over all tested assignments. 379 max-flow comparisons (old, structural and color capacities), nine strict reductions of virtual max-flow under the color capacity, 81 injective full-flow fractional weighted path checks. All assertions passed. These are capacity reductions on specified circuits, not strict improvements in minimum gate size.

Four separately constructed correlated-feedback mux topologies k=4..7: old max-flow 16,32,64,128 respectively (certifying all old cuts), refined structural port capacity 8 in each case. Actual graph supports and max flows computed, not just a numerical capacity profile. The covering-array obstruction has 17 histories and 544 partial rows. No new packed grammar checks this round; the enabled lookup/metadata replay from the previous handoff is unchanged. No new native SAT synthesis, Lean proof, or production changes. [Replay](feedback_compatibility_replay.txt).

## 7. Next mathematical target

The topology-only capacity now depends on a nested cut: a data-side vertex has virtual capacity bounded by the exponential of its smallest upstream feedback separator. This is a concrete noncircular improvement, but early independent feedback can still make it large, and the coloring refinement may depend on unknown gate semantics. The next target is a joint resource tradeoff between providing large independent feedback interfaces at many data-side gates and carrying data through those gates. Investigate whether shared upstream separators force common correlated histories for MANY response tables, not merely one, and whether a single joint code can account for those correlations without adding overlapping per-vertex charges. Compare with actual programmable sorting and mux controls, two-read compiler, and Andreev/Tseitin/cubic witness controls before claiming a superlinear bound. No claim that feedback history separators must be small in all near-linear SAT graphs. No full asymptotic solution.

Native/independent agent: audit the topological reconstruction proof, conflict graph interpretation, full-DAG feedback separator and fractional max-flow proof. Independently replay exact coloring and rejecting topologies. Consider proof of a joint cut code with shared feedback history components or a structural bound on color numbers. The covering-array example rules out a naive per-data-row history-domain substitution. Preserve the historical handoff. L-clb-036 remains open.
