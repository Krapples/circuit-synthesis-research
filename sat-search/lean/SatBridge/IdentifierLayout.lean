import SatBridge.UnitClauses
import Mathlib.Data.List.OfFn
import CircuitLemmas.BlockProduct

namespace SatBridge

open PEqualNP.Search

/-- The offset of a low identifier bit in a positive unit clause. -/
def identifierOffset (i : ℕ) : ℕ := 3 + 2 * i

/-- Read a bit of a positive identifier clause. Only the low digit positions use the input row. -/
def identifierCell (r : ℕ) (row : ℕ → Bool) (i : ℕ) : Bool :=
  if i < 2 then true
  else if i < 2 + 2 * r then
    if i % 2 = 0 then true else row ((i - 2) / 2)
  else [true, true, false, true, false, false][i - (2 + 2 * r)]?.getD false

private theorem ofFn_lowPairs (r : ℕ) (row : ℕ → Bool) :
    (List.ofFn fun j : Fin (r * 2) =>
      if (j : ℕ) % 2 = 0 then true else row ((j : ℕ) / 2)) =
      (List.ofFn fun j : Fin r => row j).flatMap (fun b => [true, b]) := by
  rw [List.ofFn_mul, List.flatMap]
  congr 1
  rw [List.map_ofFn]
  apply congrArg List.ofFn
  funext j
  rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
  simp only [Fin.val_zero, Fin.val_succ, Function.comp_apply,
    ite_eq_left (show ((j : ℕ) * 2 + 0) % 2 = 0 by omega),
    ite_eq_right (show ((j : ℕ) * 2 + (0 + 1)) % 2 ≠ 0 by omega),
    show ((j : ℕ) * 2 + (0 + 1)) / 2 = j by omega]

/-- The positive clause encoding as an array of fixed tokens and individual free bits. -/
theorem ofFn_identifierCell (r : ℕ) (row : ℕ → Bool) :
    (List.ofFn fun i : Fin (2 + r * 2 + 6) => identifierCell r row i) =
      encodeClause [(identifier (List.ofFn fun j : Fin r => row j), true)] := by
  rw [encode_identifier_unit, List.ofFn_add, List.ofFn_add]
  have hp : (List.ofFn fun i : Fin 2 => identifierCell r row i) = [true, true] := by
    simp [List.ofFn_succ, identifierCell]
  have hm : (List.ofFn fun i : Fin (r * 2) => identifierCell r row (2 + i)) =
      (List.ofFn fun j : Fin r => row j).flatMap (fun b => [true, b]) := by
    rw [← ofFn_lowPairs]
    apply congrArg List.ofFn
    funext i
    have hi := i.isLt
    simp only [identifierCell, ite_eq_right (show ¬ 2 + (i : ℕ) < 2 by omega),
      ite_eq_left (show 2 + (i : ℕ) < 2 + 2 * r by omega),
      show (2 + (i : ℕ)) % 2 = (i : ℕ) % 2 by omega, Nat.add_sub_cancel_left]
  have ht : (List.ofFn fun i : Fin 6 => identifierCell r row (2 + r * 2 + i)) =
      [true, true, false, true, false, false] := by
    apply List.ext_getElem (by simp)
    intro i hi _
    simp only [List.length_ofFn] at hi
    simp only [List.getElem_ofFn, identifierCell,
      ite_eq_right (show ¬ 2 + r * 2 + i < 2 by omega),
      ite_eq_right (show ¬ 2 + r * 2 + i < 2 + 2 * r by omega),
      show 2 + r * 2 + i - (2 + 2 * r) = i by omega]
    rw [List.getElem?_eq_getElem (by simpa using hi)]
    rfl
  simp only [Fin.val_castLE, Fin.val_natAdd, hp, hm, ht, List.append_assoc]

/-- The clause cell reads exactly its corresponding query coordinate on the low digit positions. -/
theorem identifierCell_at_offset (r : ℕ) (row : ℕ → Bool) {i : ℕ} (hi : i < r) :
    identifierCell r row (identifierOffset i) = row i := by
  simp [identifierCell, identifierOffset, show ¬ 3 + 2 * i < 2 by omega,
    show 3 + 2 * i < 2 + 2 * r by omega,
    show (3 + 2 * i - 2) / 2 = i by omega]

theorem identifierCell_fixed (r : ℕ) (row : ℕ → Bool) {i : ℕ}
    (hi : ∀ j < r, i ≠ identifierOffset j) :
    identifierCell r row i = identifierCell r (fun _ => false) i := by
  unfold identifierCell
  split
  · rfl
  split
  · split
    · rfl
    · rename_i hstart hend hodd
      exact (hi ((i - 2) / 2) (by omega) (by dsimp [identifierOffset]; omega)).elim
  · rfl

open CircuitLemmas.GateElim

/-- Free positions of the j-th query after a fixed prefix of length p. -/
def queryBlock (r p j : ℕ) : Finset ℕ :=
  (Finset.range r).image fun i => p + j * (2 + r * 2 + 6) + identifierOffset i

theorem queryBlock_card (r p j : ℕ) : (queryBlock r p j).card = r := by
  rw [queryBlock, Finset.card_image_of_injective, Finset.card_range]
  intro a b hab
  dsimp [identifierOffset] at hab
  omega

private theorem query_range {r j t : ℕ} (ht : t < 2 + r * 2 + 6) :
    j * (2 + r * 2 + 6) + t < (j + 1) * (2 + r * 2 + 6) := by
  rw [Nat.add_mul, Nat.one_mul]
  omega

theorem queryBlock_disjoint (r p i j : ℕ) (h : i ≠ j) :
    Disjoint (queryBlock r p i) (queryBlock r p j) := by
  have ordered {a b : ℕ} (hab : a < b) : Disjoint (queryBlock r p a) (queryBlock r p b) := by
    apply Finset.disjoint_left.mpr
    intro w hwa hwb
    obtain ⟨x, hx, he⟩ := Finset.mem_image.mp hwa
    obtain ⟨y, _, hf⟩ := Finset.mem_image.mp hwb
    have hxt : identifierOffset x < 2 + r * 2 + 6 := by
      rw [Finset.mem_range] at hx
      dsimp [identifierOffset]
      omega
    have ht := query_range (j := a) hxt
    have hm := Nat.mul_le_mul_right (2 + r * 2 + 6) (show a + 1 ≤ b by omega)
    omega
  rcases lt_or_gt_of_ne h with hlt | hgt
  · exact ordered hlt
  · exact (ordered hgt).symm

/-- The assignment outside the free digit positions is read from this fixed word. -/
def queryLayoutBit (pre suffix : List Bool) (r k : ℕ) (x : ℕ → Bool) (w : ℕ) : Bool :=
  let L := 2 + r * 2 + 6
  let p := pre.length
  if w < p then pre[w]?.getD false
  else if w < p + k * L then
    identifierCell r (fun i => x (p + ((w - p) / L) * L + identifierOffset i)) ((w - p) % L)
  else suffix[w - (p + k * L)]?.getD false

def queryFixed (pre suffix : List Bool) (r k : ℕ) : Finset ℕ :=
  Finset.range (pre.length + k * (2 + r * 2 + 6) + suffix.length) \
    (Finset.range k).biUnion (queryBlock r pre.length)

theorem queryBlock_lt {r k p s j w : ℕ} (hj : j < k) (hw : w ∈ queryBlock r p j) :
    w < p + k * (2 + r * 2 + 6) + s := by
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
  rw [Finset.mem_range] at hi
  have ht : identifierOffset i < 2 + r * 2 + 6 := by dsimp [identifierOffset]; omega
  have hb := query_range (j := j) ht
  have hm := Nat.mul_le_mul_right (2 + r * 2 + 6) (show j + 1 ≤ k by omega)
  omega

theorem queryFixed_card_add (pre suffix : List Bool) (r k : ℕ) :
    (queryFixed pre suffix r k).card + k * r =
      pre.length + k * (2 + r * 2 + 6) + suffix.length := by
  have hd : (↑(Finset.range k) : Set ℕ).PairwiseDisjoint (queryBlock r pre.length) := by
    intro i _ j _ hne
    exact queryBlock_disjoint r pre.length i j hne
  have hcard : ((Finset.range k).biUnion (queryBlock r pre.length)).card = k * r := by
    rw [Finset.card_biUnion hd]
    simp [queryBlock_card]
  have hsub : (Finset.range k).biUnion (queryBlock r pre.length) ⊆
      Finset.range (pre.length + k * (2 + r * 2 + 6) + suffix.length) := by
    intro w hw
    obtain ⟨j, hj, hw⟩ := Finset.mem_biUnion.mp hw
    exact Finset.mem_range.mpr (queryBlock_lt (Finset.mem_range.mp hj) hw)
  have hle := Finset.card_le_card hsub
  rw [hcard, Finset.card_range] at hle
  rw [queryFixed, Finset.card_sdiff_of_subset hsub, hcard, Finset.card_range]
  omega

private theorem queryLayout_at {pre suffix : List Bool} {r k j t : ℕ}
    (x : ℕ → Bool) (hj : j < k) (ht : t < 2 + r * 2 + 6) :
    queryLayoutBit pre suffix r k x (pre.length + j * (2 + r * 2 + 6) + t) =
      identifierCell r (fun i => x (pre.length + j * (2 + r * 2 + 6) + identifierOffset i)) t := by
  let L := 2 + r * 2 + 6
  have hL : 0 < L := by dsimp [L]; omega
  have hb := query_range (j := j) ht
  have hm := Nat.mul_le_mul_right L (show j + 1 ≤ k by omega)
  have hlt : pre.length + j * L + t < pre.length + k * L := by
    change j * L + t < (j + 1) * L at hb
    omega
  have hdiv : (j * L + t) / L = j := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hL, Nat.div_eq_of_lt ht, Nat.zero_add]
  have hmod : (j * L + t) % L = t := by
    rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt ht]
  unfold queryLayoutBit
  change (if pre.length + j * L + t < pre.length then _ else if
    pre.length + j * L + t < pre.length + k * L then _ else _) = _
  have hs : pre.length + j * L + t - pre.length = j * L + t := by omega
  rw [ite_eq_right (by omega), ite_eq_left hlt, hs, hdiv, hmod]

/-- The complete word rendered from the mask really is a coordinate restriction. -/
theorem queryLayout_fix (pre suffix : List Bool) (r k : ℕ) (x : ℕ → Bool) {w : ℕ}
    (hw : w < pre.length + k * (2 + r * 2 + 6) + suffix.length) :
    fixS (queryFixed pre suffix r k) (queryLayoutBit pre suffix r k (fun _ => false)) x w =
      queryLayoutBit pre suffix r k x w := by
  let p := pre.length
  let L := 2 + r * 2 + 6
  by_cases hF : w ∈ queryFixed pre suffix r k
  · rw [fixS, ite_eq_left hF]
    have hn : w ∉ (Finset.range k).biUnion (queryBlock r p) := (Finset.mem_sdiff.mp hF).2
    dsimp only [queryLayoutBit]
    split
    · rfl
    split
    · rename_i hp hq
      have hL : 0 < L := by dsimp [L]; omega
      have hj : (w - p) / L < k := (Nat.div_lt_iff_lt_mul hL).mpr (by
        change ¬ w < p at hp
        change w < p + k * L at hq
        omega)
      have hsum : p + ((w - p) / L) * L + (w - p) % L = w := by
        have he := Nat.div_add_mod (w - p) L
        rw [Nat.mul_comm L] at he
        change ¬ w < p at hp
        omega
      symm
      apply identifierCell_fixed
      intro i hi he
      apply hn
      refine Finset.mem_biUnion.mpr ⟨_, Finset.mem_range.mpr hj, ?_⟩
      exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, by rw [← he]; exact hsum⟩
    · rfl
  · rw [fixS, ite_eq_right hF]
    have hm : w ∈ (Finset.range k).biUnion (queryBlock r p) := by
      by_contra hn
      exact hF (Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr hw, hn⟩)
    obtain ⟨j, hj, hm⟩ := Finset.mem_biUnion.mp hm
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hm
    rw [Finset.mem_range] at hi hj
    have ht : identifierOffset i < L := by dsimp [L, identifierOffset]; omega
    rw [queryLayout_at x hj ht, identifierCell_at_offset r _ hi]

/-- Render the fixed prefix, positive identifier clauses, and fixed suffix at their exact positions. -/
theorem queryLayout_word (pre suffix : List Bool) (r k : ℕ) (x : ℕ → Bool) :
    (List.ofFn fun w : Fin (pre.length + k * (2 + r * 2 + 6) + suffix.length) =>
      queryLayoutBit pre suffix r k x w) =
      pre ++ (List.ofFn fun j : Fin k => encodeClause
        [(identifier (List.ofFn fun i : Fin r =>
          x (pre.length + (j : ℕ) * (2 + r * 2 + 6) + identifierOffset i)), true)]).flatten ++
      suffix := by
  let L := 2 + r * 2 + 6
  have hp : (List.ofFn fun w : Fin pre.length => queryLayoutBit pre suffix r k x w) =
      pre := by
    apply List.ext_getElem (by simp)
    intro w hw _
    simp only [List.length_ofFn] at hw
    simp [queryLayoutBit]
  have hq : (List.ofFn fun w : Fin (k * L) =>
      queryLayoutBit pre suffix r k x (pre.length + w)) =
      (List.ofFn fun j : Fin k => encodeClause [(identifier (List.ofFn fun i : Fin r =>
        x (pre.length + (j : ℕ) * L + identifierOffset i)), true)]).flatten := by
    rw [List.ofFn_mul]
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext j
    rw [← ofFn_identifierCell r (fun i => x (pre.length + (j : ℕ) * L + identifierOffset i))]
    apply congrArg List.ofFn
    funext t
    simpa only [L, Nat.add_assoc] using queryLayout_at (pre := pre) (suffix := suffix) x j.isLt t.isLt
  have hs : (List.ofFn fun w : Fin suffix.length =>
      queryLayoutBit pre suffix r k x (pre.length + k * L + w)) = suffix := by
    apply List.ext_getElem (by simp)
    intro w hw _
    simp only [List.length_ofFn] at hw
    simp only [List.getElem_ofFn, queryLayoutBit]
    change (if pre.length + k * L + w < pre.length then _ else if
      pre.length + k * L + w < pre.length + k * L then _ else _) = _
    rw [ite_eq_right (by omega), ite_eq_right (by omega), show
      pre.length + k * L + w - (pre.length + k * L) = w by omega,
      List.getElem?_eq_getElem hw]
    rfl
  change (List.ofFn fun w : Fin (pre.length + k * L + suffix.length) => _) =
    pre ++ (List.ofFn fun j : Fin k => encodeClause [(identifier (List.ofFn fun i : Fin r =>
      x (pre.length + (j : ℕ) * L + identifierOffset i)), true)]).flatten ++ suffix
  rw [List.ofFn_add, List.ofFn_add]
  simp only [Fin.val_castLE, Fin.val_natAdd, hp, hq, hs]

end SatBridge
