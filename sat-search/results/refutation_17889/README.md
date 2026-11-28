# L-meta-17889 is false as posted: Lean refutation (2026-11-27)

**Grade:** verified (Lean, checked locally). Released on the desk as `statement_seems_false`. No
refute twin is posted (`gap.refutation = null`), so nothing was submitted.

## The posted statement

`row17889.json` holds the desk snapshot (title: "4-cycle-free bipartite incidence: … no larger
(step 2 of 2)"). It is step 2 of 2 of a checked cut of L-meta-8181. Its sibling is L-meta-17887.

Paraphrase: for all `x1 x2`, every edge set `E ⊆ Fin x1 × Fin x2`, every `e ∈ E`, and every
circuit `C`, if `C` is `IsAO2 (x1+x2)` and computes `f_E`, then some `IsAO2` circuit `C'` with
`C'.size < C.size` computes `f_{E.erase e}`.

Here `f_E(x)` is true iff some edge `(p, l) ∈ E` has `x_p = x_{x1+l} = true`. `IsAO2` means
`AndOrOnly ∧ ReadsBack ∧ fan-in exactly 2`, and `Circuit.size = gates.length`. **The statement has
no `NoFourCycle` hypothesis.** The cut that produced it seems to have dropped it.

## Counterexample

- Take `x1 = x2 = 2`, `E = K_{2,2}` (`Finset.univ`) and `e = (0,0)`. The inputs are `p0 p1 l0 l1`
  (wires 0–3).
- `C0 = [OR 0 1, OR 2 3, AND 4 5]` with output 6 is `IsAO2`, has size 3, and computes `f_E`.
- `f_{E∖e} = p0·l1 ∨ p1·l0 ∨ p1·l1` is the path P4.
- It depends on all four inputs. These flips change its value: `0001→1001`, `0001→0101`,
  `0100→0110` and `0100→0101`.
- An `IsAO2` circuit with at most 2 gates reads at most 3 distinct inputs, so no `C'` of size
  below 3 exists.

## Proof (`L_meta_17889_refute.lean`)

`theorem not_L_meta_17889 : ¬ (<gap.statement verbatim>)`. It imports only `Mathlib` and
`PEqualNP.Defs`. A script checked that the negated proposition matches the JSON statement
character for character.

1. `C0_ao` and `C0_fun` hold by `decide`.
2. `ok C` is a Bool check of `C` on the 5 test inputs `T`.
3. `no0`, `no1` and `no2` hold by plain `decide`. Every circuit with 0, 1 or 2 gates has inputs
   bounded by `ReadsBack` and output in `Fin (5|6|7)`, and every one fails `ok`. The 2-gate case
   alone is 11200 circuits.
4. Lemmas `wires_length`, `eval_clip` and `ok_clip`: an output wire past the last gate reads
   `false`, so it can be clipped to `min o (4+k)`. Lemma `gate_form`: an `IsAO2` gate is
   `⟨and|or, [i, j]⟩`.
5. Lemma `small`: an `IsAO2` circuit with fewer than 3 gates fails `ok`. The proof splits on the
   gate list, takes the bounds from `ReadsBack`, and rewrites the clipped circuit to `mk0`, `mk1`
   or `mk2` by `rfl`.
6. Main proof: instantiate the statement at `C0`, then apply `small` with `T_spec` (the erased
   edge function equals `fp` on `T`, by `decide`).

```
'not_L_meta_17889' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The file has no `sorry`, `admit`, `axiom` or `native_decide`. A compile takes about 45 s,
mostly loading Mathlib.

`k22_enum.py` is an independent Python check. It finds 0 `IsAO2` circuits of size at most 2, over
every output wire, that compute `f_{E∖e}`.

## Reproduce

Upstream clone `pequalnp-proofs` at HEAD 8b5c59a812 (which merges upstream 58aebfffd4). From
`lean/`, run `lake build PEqualNP.Defs`, then
`lake env lean <path>/L_meta_17889_refute.lean`.

## Scope and open questions

- No counterexample without a 4-cycle was searched for.
- The 4-cycle-free version of the step is still open, and so is the soundness of the parent cut
  (L-meta-8181) and of the sibling L-meta-17887.
