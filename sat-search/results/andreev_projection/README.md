# Andreev SAT projection and path multiplicity

Audited handoff [822b444](https://github.com/Krapples/circuit-synthesis-research/commit/822b44415b0ad68318fd98179a3eeb64bae9b7cd).
The target is the paired binary encoding used by the repository. Circuits are
single-output binary AIGs with signed edges and constants. A path counts operand
occurrences, including both reads when a consumer repeats an operand.

## Encoding and formula consequence

Let M = 2^k and r = floor(M/k). Fix the clause layout that pins M data bits and
kr selector bits, computes the k row parities and then the address-selected data
bit, and asserts the output. The only free positions are the unit polarities.
For either gate type the four clauses have exactly the allowed gate-output value
for any operands. Induction in topological order gives a unique valuation on the
numbered wires of the pinned circuit before the output assertion. The assertion
therefore accepts exactly when the addressed data bit is one. The grammar uses
LSB-first canonical identifiers, including the empty identifier for zero.

The chain/tree schedule has q = k(r−1) + M−1 auxiliary variables. There are
M+kr+1+4q clauses and M+kr+1+12q literal occurrences. All identifiers are below
4M and at least M/2 data pins use k identifier digits. Together these give even
length L(k) = Θ(kM), independent of the polarity bits. Fixed tautological
clauses on identifiers 0 and 1 have lengths 10 and 14. For even t ≥ 48, take
the coefficient of 14 to be 0, 3, 1, 4, or 2 when t modulo 10 is respectively
0, 2, 4, 6, or 8. Its cost is at most t in every case, and the remainder is a
nonnegative multiple of 10. The appended word preserves SAT and all free
coordinates. Taking the largest k with L(k)+48 ≤ n works because L(k) tends to
infinity and L(k+1)/L(k) stays bounded. The predecessor argument needs no
monotonicity of the exact lengths.

For the formula bound, fix a k-bit data table requiring Ω(M/log k) signed
De Morgan formula leaves, by counting labeled full binary trees.
Under an independent random restriction retaining each selector bit with
probability p = ln(2k)/r, the probability some row loses all of its free bits is
at most k exp(−pr) = 1/2. Otherwise further restriction to one surviving bit
per row realizes the data table with some input phases flipped. A formula's
size cannot increase under these further restrictions, and input phase changes
are free in the signed formula measure. Apply the external shrinkage theorem in
the form E[L(f restricted)] ≤ O(p²L(f)+1). This yields
Ω(M³/(k²(log k)³)) for the lookup. Substituting L(k) = Θ(kM) and padding yields
Ω(n³/((log n)^5(log log n)^3)) for paired SAT at all sufficiently large even n.
The same substitution into a formula on the balanced promise is valid, since
both signed rails may become signed input leaves. The independent-restriction
premise is from [Tal, ECCC TR14-048 revision 1](https://eccc.weizmann.ac.il/report/2014/048/).
The handoff's secondary link to TR15-062 points to a different paper. The
argument uses the primary source.

## Distinct gates and selector-only sharing

For any such circuit, let p(g) count paths from g to the output, giving the
output gate its empty path. The unfolded signed De Morgan formula has one
binary node per occurrence of each gate, so its leaf count is 1 + sum p(g).
Its depth is the longest binary path in the output cone. This forces
max p(g) = Ω(n^1.99/((log n)^5(log log n)^3)) in any hypothetical
O(n^1.01)-gate AIG for paired SAT. It counts paths in the original circuit
and does not charge a distinct gate for each path.

The Andreev restriction itself gives a stronger obstruction to such a charge.
Use balanced XOR trees for the k row parities and an ordinary mux tree for
selection, with three ANDs per XOR or mux. The circuit has 3q < 6M gates.
Each mux reads each data operand once, and every one of its three gates has a
data ancestor. Each such gate has exactly one path to the output. The address
operand feeds two ANDs per mux. The least significant row is used at M/2
muxes and hence its output wire has M paths. Each operand of a three-AND XOR
has two paths to that XOR's output. A deepest internal XOR output in the
balanced row tree is at least floor(log₂ r)−1 XOR levels below the row output.
It has Ω(Mr) output paths entirely through shared selector computation up to
the muxes. All gates are live. All source bits are essential as well. Fix the
selector to address a given data bit to witness its essentiality. To witness
essentiality of a selector bit, set the data table equal to that row's address
bit, leaving the row parity at the output.

Writing T(r) for the parity tree's unfolded leaf count gives T(1)=1 and
T(r)=2T(floor(r/2))+2T(ceil(r/2)). Every primary contributes 2^h leaves at
XOR-tree depth h, which is floor(log₂ r) or ceil(log₂ r). Hence T(r)=Θ(r²).
The whole unfolding has M + 2(M−1)T(r) leaves because each mux uses both
data children once and its selector twice. The near-cubic unfolding can
therefore coexist with a data-ancestor subgraph that is a tree, even on an
actual SAT projection padded to a prescribed even length. The obstruction
also applies to any universal argument that would charge near-cubic path
counts to distinct gates based solely on the formula lower bound and
dependence on both data and address variables. The constructed small circuit
realizes the restriction. The question of how circuits for full SAT jointly
handle restrictions that vary clause structure or identifiers remains open.
L-clb-036 remains open.

A multiple-restriction accounting attempt can be stated precisely. Given t
coordinate projections, perform only constant/alias substitution and trim
after each. Each remaining gate has an original gate ID. Set p_i(g) to its
output-path count in restriction i, or zero if it vanished. If each restricted
function requires at least B_i leaves, then
sum_i (B_i−1) ≤ sum_g sum_i p_i(g).
A per-gate upper bound U on the inner sum would imply
s ≥ sum_i (B_i−1)/U. Monotonicity under restriction alone only bounds
p_i(g) by the corresponding unrestricted multiplicity and gives no useful U.
A SAT-specific argument would have to control simultaneously surviving paths
under restrictions that change more than the data table on a common selector
skeleton. The Andreev audit supplies no such control.

## Lean scope

- [LookupProjection.lean](../../lean/SatBridge/LookupProjection.lean) checks the
  four-clause XOR and mux encodings in the repository's SAT language. It checks
  uniqueness on the numbered wires, the output assertion, one free polarity
  per source in the exact paired layout, a grammar length bound, and
  satisfiability-preserving padding to every greater even length with at least
  48 bits of slack.
- [ParityLookup.lean](../../lean/SatBridge/ParityLookup.lean) constructs the
  Andreev lookup with the shared parity rows and the exact number of XOR and
  mux gates. Its auxiliary IDs follow a depth-first topological traversal
  of the mux tree. The handoff replay uses the original level-by-level ordering.
  The generic encoding proof applies to either order. The theorem
  `andreev_padded_at_scale` chooses k at the required scale for each even
  n ≥ 1248, using the budget 300(k+1)2^k. This is a construction threshold.
- [Unfold.lean](../../lean/CircuitLemmas/Unfold.lean) checks evaluation, exact
  binary depth in the output cone, and the identity
  'leaves = 1 + sum of internal output-path counts'. It derives the depth and
  gate-count-times-multiplicity inequalities in the repository's free-phase
  AIG model. The checked count is a recursive definition by operand
  occurrence. The backwards sweep is exercised in the finite replay.
- Tal's shrinkage theorem and the resulting asymptotic formula estimate are
  paper mathematics. They are outside the Lean statements and introduce
  no new Lean axiom.
  [Build and axiom output](lean_replay.txt)

## Reproduction

Run from the repository root.

```powershell
python -B sat-search/workflow/research.py run sat-search/results/andreev_projection/batch.json --workers 1 --memory-mib 256
```

The checker hashes and replays the first Python block of the pinned handoff.
The run reproduced 2,336 SAT-semantic assignment checks across the original
and balanced encodings, 1,168 paired-rail checks, 16,256 restricted-table rows
over 448 contexts, 532 padding checks, and 2,000 unfolding checks.
The independent AIG checker evaluated 592 inputs, exhausting k ≤ 2 and
sampling k from 3 to 12, and computed path counts on all twelve networks.
For k=12 it measured 24,525 gates, 1,071,387,136 unfolded leaves, and
maximum path multiplicity 1,048,576. The maximum over data-ancestor gates
was one for all twelve networks. The bounded batch completed in 5.881 seconds.
[Raw output](replay.txt) · [Runner manifest](batch.json) ·
[Checker](../../experiments/andreev_projection_check.py)
