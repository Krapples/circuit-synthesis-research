# Live internal NOT on a six-input monotone table

L-meta-16102 requests a circuit of at most nine gates for the little-endian truth table
`18445899635892944896`. The ON-set has inclusion-minimal masks `19, 21, 22, 24, 34, 36, 40`.
Every gate must be read by a later gate or designate the output. At least one NOT must read
a gate as its first operand, and a NOT cannot read a NOT in that position. The ambient Lean definition
permits zero, one, or two inputs on each AND, OR, or NOT. A NOT ignores its second input
semantically even though that position is a syntactic reader for the step.

Lean 4.36.0 checked the eight-gate AND/OR construction in [Monotone8.lean](Monotone8.lean)
on all 64 rows with `decide +kernel`. For inputs `a,b,c,d,e,f` in wire order, the circuit is
`(d OR b OR c) AND (f OR (e AND (a OR d OR (b AND c))))` with the indicated eight binary gates.
The axiom report was `propext`, `Classical.choice`, and `Quot.sound`.

## Direct coverage of the posted gate rules

All six inputs are essential. A semantically live cone with six essential inputs needs at
least five binary gates. If a live NOT occurs, it consumes a gate with only one semantic input,
so six gates are needed. If every NOT is outside the semantic cone, at least one gate is outside
that cone and six gates are needed again. Thus sizes below six cannot satisfy the statement.

The direct encoding covers sizes six through nine. The syntactic reader condition forces the
final gate to be the output. Each operand selector ranges over earlier wires and an absent
operand. AND/OR may sort their operand list and replace duplicate operands by one occurrence
without changing semantics or any reader relation. A NOT uses only its first operand in the
row equations. Both listed operands count in the reader clauses, and a first operand that is
itself a NOT is forbidden when it refers to a gate.

Gates use an order with nondecreasing largest referenced wire. Greedily choosing a ready gate
with the smallest such index gives this order, because any newly ready gate references the
gate just appended. The first-gate shards use the two input automorphisms, the identity and
swap `(1 2)`. Under this swap the chosen representative of each first-gate orbit has minimum
largest operand index. Choose a first ready gate with the globally minimum such index over both
permutations and move it to the first position in its representative labeling. Any other ready
gate with a smaller index there would contradict global minimality. This gives coverage of the
symmetry-restricted order as well as the raw first-gate orbits.

## Normalization cross-check

The repository encoder excludes all normalized circuits of size at most nine with an internal
NOT, and all normalized circuits of size at most eight with one or more raw-input NOTs and no
internal NOT. It also excludes pure AND/OR circuits of size at most seven. The five-gate lower
bound from essential inputs covers the remaining smaller pure sizes.

To relate these checks to the posted syntax, propagate constants and identities, remove
second NOT operands, eliminate double NOTs, and keep the live output cone. If a surviving NOT
reads a gate, the normalized search applies. If surviving NOTs read only inputs, at least one
gate must have been removed. Indeed, the original required internal NOT was removed or its
first operand became an alias of an input. The resulting size is at most eight. Finally,
suppose all surviving gates are AND/OR. The pure lower bound requires eight gates. At most one
gate was removed, so the only removed gate must be the original internal NOT. With every
other gate retained, its first operand still refers to a proper gate and its listed reader
still receives it as a semantic operand of an AND or OR, unless it is itself the output.
In each case it would survive normalization. This rules out the final case.

## Solver records

All runs used MapleChrono and 22 worker processes. The times below are per job, and each
search included all 64 rows. The exclusion is an independently corroborated computational
result. The runs did not retain DRUP proof certificates.

| Encoding | Covered scope | UNSAT | Longest job | Total conflicts |
| --- | --- | ---: | ---: | ---: |
| Direct | Sizes 6–8 unsharded and all 61 first-gate orbits at size 9 | 64 | 94.40 s | 27,599,322 |
| Normalized internal NOT | Sizes 6–8 unsharded and all 27 first-gate orbits at size 9 | 30 | 37.96 s | 6,487,771 |
| Normalization controls | Pure sizes 5–7 and raw-input NOT sizes 6–8 | 32 | 6.17 s | 1,789,906 |

From the repository root with its configured Python SAT dependencies, use fresh output paths.

```powershell
$probe = 'sat-search/results/mid_not_16102'
python "$probe/search-16102-full.py" sat-search/logs/16102-full-replay.jsonl
python "$probe/search-16102.py" sat-search/logs/16102-typed-replay.jsonl
python "$probe/search-16102-normalization-controls.py" sat-search/logs/16102-controls-replay.jsonl
```

## Two-fork structural advance and certificate replay (2026-11-26)

[New paper proof](two_fork_handoff.md): the target needs **at least eight proper binary AND/OR gates even with free negations**, attained by the existing eight-gate monotone witness. The live fanout excess is b-5 for b binary gates. The first fork must carry a signed singleton input (all 63 residual-subset checks); fixing that primary eliminates the one-fork case, via a non-read-once cofactor for every input. Two forks give an exact formula-forest decomposition, including nested forks. [Standalone checker](two_fork_check.js) excludes all independent and nested templates; [replay](two_fork_replay.json) records 12,774,316 direct formula comparisons, 186 nested subset checks, 17 retained templates, 14 consistent upstream tables, and zero matching partial downstream specifications. An independent preliminary C++/Python implementation agrees. This is a paper proof with executed exact finite checks, not Lean verification.

Consequently any posted at-most-nine candidate must have exactly eight live genuine binary gates and one live internal NOT (not the output); degenerate or signed-equivalent binary gates cannot occur. The NOT's ignored second operand can be deleted, and every primary must have a path to output avoiding the NOT. Only fanout excess three remains. The previous computational UNSAT results for this final case remain valid evidence, not a checked proof.

[Certificate runner](certify-nine-gate.py) imports the archived full-syntax encoder and adds precisely the above necessary syntax and bypass-path clauses. The 22 first-gate representatives are the binary AND/OR pairs under the input automorphism. Its constraint self-test was replayed independently in Python (same two functions, no solver dependency): 14,400 toy syntaxes, 736 accepted, 13,664 rejected, 14,336 exhaustive negative path-flag checks. [Output](nine_gate_constraint_selftest.json). The full runner requires the native PySAT environment and an independently installed DRAT verifier; **the 22 actual certificate solves have not been run here**. The solver output and proof trace hashes plus verifier result are retained per shard; independent CNF verification is still not a Lean encoding-soundness theorem.

From this directory (native environment):

```sh
node two_fork_check.js
python certify-nine-gate.py --self-test
python certify-nine-gate.py --out proof-shards --solver glucose4 --timeout 300 --proof-checker drat-trim
````

The runner supports repeated `--job 0` through `--job 21` in separate fresh output directories. A complete proof must cover all 22, including any timed-out shards, and prove the circuit-to-CNF mapping under the posted syntax, or replace the CNF route with a formal three-excess argument. No upstream PR opened: live desk exact statement unavailable in this session, open PR search found no match but did not certify absence, and no Lean toolchain here. Z3's initial internal DRAT validation failed; with several simplifications disabled a six-gate query timed out. Neither is claimed as a certificate. Continue L-clb-036 separately.
