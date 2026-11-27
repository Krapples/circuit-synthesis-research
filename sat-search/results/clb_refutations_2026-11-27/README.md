# L-clb-123 and L-clb-124 are false: Lean refutation from L-clb-120 (2026-11-27)

**Grade:** checked Lean proof, compiled locally. Nothing has been submitted to the desk.

## The posted statements

L-clb-123 and L-clb-124 (`row123.json`, `row124.json`, desk snapshot of 2026-11-27T23:18Z) are
`find` statements. Each asks for a fan-in-two AND/OR/NOT circuit for cyclic count parity with
window w = 1 and few AND/OR gates:

| statement | sites n | posted bound | floor from L-clb-120 |
| --- | --- | --- | --- |
| L-clb-123 | 3 | ≤ 16 | 17 |
| L-clb-124 | 4 | ≤ 20 | 21 |

## Why they are false

The checked theorem `PEqualNP.Outside.L_clb_120` gives, for every admissible H and every fitting
circuit C:

    binary C ≥ (E − H) + 3(H − 1)

At w = 1, J = 2^min(n, 2) = 4, so H = 4 is admissible through the `H ≤ J` disjunct.

- n = 3: E = 12, so the floor is 8 + 9 = 17.
- n = 4: E = 16, so the floor is 12 + 9 = 21.

The definitions of `inv`, `binary` and `fits` in the posted statements match L-clb-120's
definitions textually. The only difference is how `loc` proves its bound: `Nat.succ_pos 2` versus
`hn`. Proof irrelevance makes the two definitionally equal. The desk context itself says that
"a hand-back saying the floor stands is useful data".

## Proof

`Refute_clb_123_124.lean` proves `¬ (<posted statement>)` for both statements. Each negated
proposition is generated verbatim from the desk JSON. Each proof is four steps:

1. Instantiate L-clb-120 at (n, 1, H = 4).
2. Coerce the bound to `17 ≤ size − #NOT` (21 at n = 4) by definitional unfolding.
3. Coerce `hb` the same way.
4. Close with `omega`.

The first compile showed that `omega` could not see through the un-beta-reduced `binary` lambda in
`hb`. Step 3 is the fix.

```
'not_L_clb_123' depends on axioms: [propext, Classical.choice, Quot.sound]
'not_L_clb_124' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Reproduce

1. `gh repo clone open-goat/pequalnp-proofs upstream -- --depth 1`. The proof was checked against
   upstream commit ff663328a6f909127d1f22fcb4668e7d02a1ec0a.
2. Junction `upstream/lean/.lake/packages` to `sat-search/lean/.lake/packages`. The Mathlib and
   dependency revisions are identical, so the existing build is reused.
3. Copy the `.lean` file to `lean/PEqualNP/Outside/`.
4. In `lean/`, run `lake build PEqualNP.Outside.L_clb_120` (about 7.5 min).
5. Run `lake env lean PEqualNP/Outside/Refute_clb_123_124.lean` (about 20 s).

## Desk action (not taken)

When the units are offerable, release them with `statement_seems_false` and cite L-clb-120. This
needs the user's authorization. The statements themselves cannot be proved.
