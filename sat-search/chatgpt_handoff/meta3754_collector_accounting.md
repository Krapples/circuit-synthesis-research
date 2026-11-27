# L-meta-3754 clean OR collector accounting

This continues the [one-junk paper proof](meta3754_one_junk_complete_handoff.md)
in the upstream `IsAO2`, `IsLeastAO`, and `IsLiftFixedPoint` model.
The [verification run at `9608613`](https://github.com/Krapples/circuit-synthesis-research/actions/runs/45950896126)
includes `allLive`, `cleanWireReader`, the suspended-gate collector semantics,
the singleton-overlap/no-exposure strict deletion, and the separate filtered
provider compiler.

## Exact count

In [OneJunkErase.lean](lean/OneJunkErase.lean), `cleanGates` counts original
gate indices by operator and by the upstream `BelowF` predicate. Write `T`
for the number of clean AND gates and `O` for the number of clean OR gates.

- `collectorOrLower` proves `T ≤ O + 1`. Every clean gate other than the
  output is read by a clean OR. Its wire therefore appears among the at most
  `2O` distinct input wires of the clean OR gates. Together with the output
  this covers the `T + O` clean gate wires. This argument allows fan-out.
- `collectorOrExact` proves `O = T - 1` with natural-number subtraction.
  With gates present, the output is a gate and there is at least one clean
  AND. The gates kept when deleting the clean ORs form an ancestor-closed
  selection, because only clean ORs read clean wires. The proof compiles
  that selection into a fresh gate list while preserving all retained wire
  values. It then joins the original clean AND values with a chain of
  exactly `T - 1` binary OR gates. Collector semantics gives the same
  output function, so leastness gives the reverse inequality. The empty
  gate list is handled separately.

The count uses no unique-junk, bipartite, or C4-free assumption. For a
one-junk replacement it supplies the exact original collector budget. A
replacement still has to prove which tops can be removed or replaced and
which provider gates can be preserved or rebuilt. The next subcase is the
multiple-vertex overlap, where the checked filter plan needs to be attached
to the concrete retained provider cones and their stable wire remapping.

## Reproduction

Use the [locked research environment](lean_verification_handoff.md) with
upstream `3db0136bf094e975baaf20214b01e4b4579059f2`, Lean `v4.36.0`, and
Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. From that upstream
checkout's `lean` directory, after `lake build PEqualNP.Defs`, run the
same command as the research workflow:

```powershell
lake env lean -DwarningAsError=true <absolute-path-to-OneJunkErase.lean>
```

The strict local check passed in 48.721 seconds. The transitive audit of all
22 printed declarations found only `propext`, `Classical.choice`, and
`Quot.sound`. The checked proof source has SHA-256
`82e60f94f22227ceb9cd146d02476828380392aa3a3860d0728bdf04130f4371`.
The upstream submission checker and the full one-junk theorem remain open.
