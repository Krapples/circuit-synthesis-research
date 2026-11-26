/-
End-to-end SAT lower bound at lengths divisible by six (2026-11-26).

`sat_six_lower`: every fan-in-two AND/OR/NOT circuit of the external library (NOT gates counted) that
decides `PEqualNP.Search.SAT` at length `6 * (q + 1)`, `q ≥ 1`, has at least `8 * q + 5` gates, i.e.
`D.size ≥ 8Q - 3 = 4n/3 - 3` at `n = 6Q`, `Q ≥ 2`.

Chain: the six-bit identity (`SixBit.word_mem_sat`) shows that fixing the `4q + 6` positions outside the
pairs `(6j+2, 6j+5)` to the pattern `11·10·` ... `110100` leaves the XNOR conjunction of `q` disjoint pairs;
the external L037 makes every fixed input essential; the model transfer (`Transfer.transfer`) moves the
circuit into the free-NOT AIG model, where `xnorConj_restriction_lower` (excess restriction plus
`C(F_q) >= 4q - 1`) gives `|F| + 4q - 1` gates.
-/
import SatBridge.Transfer
import SatBridge.SixBit
import PEqualNP.CircuitLowerBounds.L037
import CircuitLemmas.Composition

namespace SatBridge

open CircuitLemmas.GateElim PEqualNP.Search

/-! ### The fixed positions -/

/-- The fixed positions of the first `j` blocks: offsets `0, 1, 3, 4`. -/
def blocksF : ℕ → Finset ℕ
  | 0 => ∅
  | j + 1 => blocksF j ∪ {6 * j, 6 * j + 1, 6 * j + 3, 6 * j + 4}

theorem mem_blocksF : ∀ (q i : ℕ), i ∈ blocksF q ↔ i < 6 * q ∧ (i % 6 = 0 ∨ i % 6 = 1 ∨ i % 6 = 3 ∨ i % 6 = 4)
  | 0, i => by simp [blocksF]
  | q + 1, i => by
      simp only [blocksF, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, mem_blocksF q i]
      omega

theorem card_blocksF : ∀ q, (blocksF q).card = 4 * q
  | 0 => rfl
  | q + 1 => by
      rw [blocksF, Finset.card_union_of_disjoint, card_blocksF q]
      · have : ({6 * q, 6 * q + 1, 6 * q + 3, 6 * q + 4} : Finset ℕ).card = 4 := by
          rw [Finset.card_insert_of_notMem (by simp), Finset.card_insert_of_notMem (by simp),
            Finset.card_pair (by omega)]
        omega
      · rw [Finset.disjoint_left]
        intro a ha hb
        rw [mem_blocksF] at ha
        simp only [Finset.mem_insert, Finset.mem_singleton] at hb
        omega

/-- All fixed positions: the blocks and the six tail positions. -/
def fixedF (q : ℕ) : Finset ℕ := blocksF q ∪ Finset.Ico (6 * q) (6 * q + 6)

theorem mem_fixedF (q i : ℕ) : i ∈ fixedF q ↔
    (i < 6 * q ∧ (i % 6 = 0 ∨ i % 6 = 1 ∨ i % 6 = 3 ∨ i % 6 = 4)) ∨ (6 * q ≤ i ∧ i < 6 * q + 6) := by
  simp [fixedF, mem_blocksF]

theorem card_fixedF (q : ℕ) : (fixedF q).card = 4 * q + 6 := by
  rw [fixedF, Finset.card_union_of_disjoint, card_blocksF]
  · simp
  · rw [Finset.disjoint_left]
    intro a ha hb
    rw [mem_blocksF] at ha
    simp only [Finset.mem_Ico] at hb
    omega

/-- The fixed values: `1 1 · 1 0 ·` in the blocks, `1 1 0 1 0 0` in the tail. -/
def fixedB (q : ℕ) (i : ℕ) : Bool :=
  if 6 * q ≤ i then tail.getD (i - 6 * q) false else decide (i % 6 ≠ 4)

theorem fixS_val (q : ℕ) (y : ℕ → Bool) (i : ℕ) :
    fixS (fixedF q) (fixedB q) y i =
      if i < 6 * q then (if i % 6 = 2 ∨ i % 6 = 5 then y i else decide (i % 6 ≠ 4))
      else if i < 6 * q + 6 then tail.getD (i - 6 * q) false else y i := by
  unfold fixS fixedB
  by_cases hi : i ∈ fixedF q
  · rw [if_pos hi]
    rw [mem_fixedF] at hi
    split_ifs <;> first | rfl | omega
  · rw [if_neg hi]
    rw [mem_fixedF] at hi
    split_ifs <;> first | rfl | omega

/-! ### The restricted string -/

theorem ofFn_eq_map (m : ℕ) (g : ℕ → Bool) : (List.ofFn fun i : Fin m => g i) = (List.range m).map g := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

theorem range_six (g : ℕ → Bool) : ∀ q, (List.range (6 * q)).map g =
    (List.range q).flatMap fun j => [g (6 * j), g (6 * j + 1), g (6 * j + 2), g (6 * j + 3),
      g (6 * j + 4), g (6 * j + 5)]
  | 0 => rfl
  | q + 1 => by
      rw [show 6 * (q + 1) = 6 * q + 6 by ring, List.range_add, List.map_append, range_six g q,
        List.range_succ (n := q), List.flatMap_append]
      simp [List.range_succ, Nat.add_assoc]

theorem restricted_word (q : ℕ) (y : ℕ → Bool) :
    (List.ofFn fun i : Fin (6 * (q + 1)) => fixS (fixedF q) (fixedB q) y i) =
      word ((List.range q).map fun j => (y (6 * j + 2), y (6 * j + 5))) := by
  rw [ofFn_eq_map, show 6 * (q + 1) = 6 * q + 6 by ring, List.range_add, List.map_append, range_six,
    word, List.flatMap_map]
  congr 1
  · apply List.flatMap_congr
    intro j hj
    rw [List.mem_range] at hj
    simp only [fixS_val, blk]
    rw [if_pos (by omega), if_neg (by omega), if_pos (by omega), if_neg (by omega),
      if_pos (by omega), if_pos (by omega), if_pos (by omega), if_neg (by omega),
      if_pos (by omega), if_neg (by omega), if_pos (by omega), if_pos (by omega)]
    rw [show 6 * j % 6 = 0 by omega, show (6 * j + 1) % 6 = 1 by omega, show (6 * j + 3) % 6 = 3 by omega,
      show (6 * j + 4) % 6 = 4 by omega]
    rfl
  · simp [List.range_succ, fixS_val, tail]

/-! ### Pairs -/

def pairs (q : ℕ) : List (ℕ × ℕ) := (List.range q).map fun j => (6 * j + 2, 6 * j + 5)

theorem pairs_nodup (q : ℕ) : CircuitLemmas.GateElim.PairsNodup (pairs q) := by
  unfold CircuitLemmas.GateElim.PairsNodup pairs
  rw [List.flatMap_map]
  refine List.nodup_flatMap.2 ⟨fun j _ => by simp, ?_⟩
  refine (List.pairwise_lt_range).imp fun {a b} hab => ?_
  intro u hu hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu hv
  omega

theorem pairs_length (q : ℕ) : (pairs q).length = q := by simp [pairs]

theorem xnorConj_pairs (q : ℕ) (y : ℕ → Bool) :
    xnorConj (pairs q) y = true ↔
      ∀ p ∈ (List.range q).map (fun j => (y (6 * j + 2), y (6 * j + 5))), p.1 = p.2 := by
  simp [xnorConj, pairs]

/-! ### Essential inputs from L037 -/

theorem essential_of_L037 (q : ℕ) (hq : 1 ≤ q) (D : PEqualNP.CircuitLowerBounds.Circuit)
    (hdec : D.Decides SAT (6 * (q + 1))) (z : ℕ) (hz : z < 6 * (q + 1)) :
    ∃ x : ℕ → Bool, (fun y : ℕ → Bool => D.eval (List.ofFn fun i : Fin (6 * (q + 1)) => y i)) (upd x z true) ≠
      (fun y : ℕ → Bool => D.eval (List.ofFn fun i : Fin (6 * (q + 1)) => y i)) (upd x z false) := by
  obtain ⟨x, hx⟩ := PEqualNP.CircuitLowerBounds.L037 (q + 1) (by omega) ⟨z, hz⟩
  refine ⟨fun j => if h : j < 6 * (q + 1) then x ⟨j, h⟩ else false, ?_⟩
  have key : ∀ c : Bool, (List.ofFn fun i : Fin (6 * (q + 1)) =>
      upd (fun j => if h : j < 6 * (q + 1) then x ⟨j, h⟩ else false) z c i) =
      List.ofFn (Function.update x ⟨z, hz⟩ c) := by
    intro c
    congr 1
    funext i
    simp only [upd, Function.update, i.2, dite_true]
    by_cases h : (i : ℕ) = z
    · have : i = ⟨z, hz⟩ := Fin.ext h
      simp [h, this]
    · have : i ≠ ⟨z, hz⟩ := fun e => h (by rw [e])
      simp [h, this]
  simp only [key]
  intro heq
  have hall : ∀ c, D.eval (List.ofFn (Function.update x ⟨z, hz⟩ c)) =
      D.eval (List.ofFn (Function.update x ⟨z, hz⟩ true)) := by
    intro c; cases c
    · exact heq.symm
    · rfl
  have h1 := hdec (List.ofFn (Function.update x ⟨z, hz⟩ (!x ⟨z, hz⟩))) List.length_ofFn
  have h2 := hdec (List.ofFn x) List.length_ofFn
  have e : D.eval (List.ofFn (Function.update x ⟨z, hz⟩ (!x ⟨z, hz⟩))) = D.eval (List.ofFn x) := by
    rw [hall, ← hall (x ⟨z, hz⟩), Function.update_eq_self]
  rw [e] at h1
  rw [← h1, ← h2] at hx
  simp at hx

/-! ### The bound -/

/-- **End-to-end SAT bound at lengths `6(q+1)`.** A fan-in-two AND/OR/NOT circuit deciding SAT at length
`6 * (q + 1)`, `q ≥ 1`, has at least `8 * q + 5` gates (NOT gates counted). -/
theorem sat_six_lower (q : ℕ) (hq : 1 ≤ q) (D : PEqualNP.CircuitLowerBounds.Circuit)
    (hD : ∀ g ∈ D.gates, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} :
        Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2)
    (hdec : D.Decides SAT (6 * (q + 1))) : 8 * q + 5 ≤ D.size := by
  have hR := transfer (6 * (q + 1)) D hD
  have hFn : ∀ z ∈ fixedF q, z < 6 * (q + 1) := by
    intro z hz; rw [mem_fixedF] at hz; omega
  have hres : ∀ y, (fun y : ℕ → Bool => D.eval (List.ofFn fun i : Fin (6 * (q + 1)) => y i))
      (fixS (fixedF q) (fixedB q) y) = xnorConj (pairs q) y := by
    intro y
    simp only
    apply Bool.eq_iff_iff.2
    rw [hdec _ List.length_ofFn, restricted_word, word_mem_sat, xnorConj_pairs]
  have hP : pairs q ≠ [] := by
    intro h; have := congrArg List.length h; rw [pairs_length] at this; simp at this; omega
  have hlt : ∀ p ∈ pairs q, p.1 < 6 * (q + 1) ∧ p.2 < 6 * (q + 1) := by
    intro p hp; simp only [pairs, List.mem_map, List.mem_range] at hp
    obtain ⟨j, hj, rfl⟩ := hp; constructor <;> simp <;> omega
  have := xnorConj_restriction_lower (fixedF q) (fixedB q) (pairs q) hP hlt (pairs_nodup q) hFn
    (fun z hz => essential_of_L037 q hq D hdec z (hFn z hz)) hres hR
  rw [card_fixedF, pairs_length] at this
  omega

/-- The bound in the form of L037: at length `6 * Q`, `Q ≥ 2`, at least `8 * Q - 3` gates. -/
theorem sat_six_lower' (Q : ℕ) (hQ : 2 ≤ Q) (D : PEqualNP.CircuitLowerBounds.Circuit)
    (hD : ∀ g ∈ D.gates, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} :
        Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2)
    (hdec : D.Decides SAT (6 * Q)) : 8 * Q ≤ D.size + 3 := by
  obtain ⟨q, rfl⟩ : ∃ q, Q = q + 1 := ⟨Q - 1, by omega⟩
  have := sat_six_lower q (by omega) D hD hdec
  omega

/-- No size bound with slope `1.33` (`100 * s n ≤ 133 * n + c`) puts SAT in `SIZE s`. -/
theorem sat_not_size_133 : ¬ ∃ (s : ℕ → ℕ) (c : ℕ), (∀ n : ℕ, 100 * s n ≤ 133 * n + c) ∧
    SAT ∈ PEqualNP.CircuitLowerBounds.SIZE s := by
  rintro ⟨s, c, hs, hS⟩
  obtain ⟨D, hD, hsz, hdec⟩ := hS (6 * (c + 200))
  have h1 := sat_six_lower' (c + 200) (by omega) D hD hdec
  have h2 := hs (6 * (c + 200))
  omega

end SatBridge
