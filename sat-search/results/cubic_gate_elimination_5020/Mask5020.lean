import Mathlib
import PEqualNP.Defs

namespace Mask5020

variable {n : ℕ} {G : SimpleGraph (Fin n)} {A : Finset (Fin n)}
variable {f : (Fin n → Bool) → Bool}

def input (S : Finset (Fin n)) : Fin n → Bool :=
  fun i => decide (i ∈ S)

def edgeSpec (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x, f x = true ↔ (∃ a ∈ A, x a = true) ∨
    ∃ i j, G.Adj i j ∧ x i = true ∧ x j = true

theorem off_on (hf : edgeSpec G A f)
    {v w : Fin n} {S : Finset (Fin n)}
    (hS : ∀ i ∈ S, i ∉ A)
    (hInd : ∀ i ∈ S, ∀ j ∈ S, ¬ G.Adj i j)
    (hvw : G.Adj v w) (hw : w ∈ S) :
    f (input S) = false ∧ f (input (insert v S)) = true := by
  constructor
  · cases h : f (input S)
    · rfl
    · rcases (hf (input S)).1 h with ⟨a, ha, hs⟩ | ⟨i, j, hij, hi, hj⟩
      · exact (hS a (by simpa [input] using hs) ha).elim
      · exact (hInd i (by simpa [input] using hi) j (by simpa [input] using hj) hij).elim
  · exact (hf _).2 (Or.inr ⟨v, w, hvw, by simp [input], by simp [input, hw]⟩)

theorem two_and_witness {v a b : Fin n}
    (hf : edgeSpec G A f) (hA : ∀ i j, G.Adj i j → i ∉ A)
    (hdeg : (G.neighborSet v).ncard = 3) :
    ∃ S : Finset (Fin n), v ∉ S ∧ a ∉ S ∧ b ∉ S ∧
      f (input S) = false ∧ f (input (insert v S)) = true := by
  classical
  have hw : ∃ w, G.Adj v w ∧ w ≠ a ∧ w ≠ b := by
    by_contra! h
    have hsub : G.neighborSet v ⊆ (↑({a, b} : Finset (Fin n)) : Set (Fin n)) := by
      intro w hw
      have hw' : G.Adj v w := hw
      by_cases ha : w = a
      · simp [ha]
      · have hb : w = b := h w hw' ha
        simp [hb]
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [hdeg, Set.ncard_coe_finset] at hle
    have ht := Finset.card_insert_le a ({b} : Finset (Fin n))
    simp only [Finset.card_singleton] at ht
    omega
  obtain ⟨w, hvw, hwa, hwb⟩ := hw
  have hvw' : v ≠ w := hvw.ne
  have hwA := hA w v hvw.symm
  refine ⟨{w}, by simpa using hvw', by simpa using Ne.symm hwa,
    by simpa using Ne.symm hwb, ?_⟩
  apply off_on hf (S := {w}) _ _ hvw (by simp)
  · simpa using hwA
  · simp

theorem and_or_witness {v a b : Fin n}
    (hf : edgeSpec G A f) (hA : ∀ i j, G.Adj i j → i ∉ A)
    (hdeg : (G.neighborSet v).ncard = 3) (hbA : b ∉ A)
    (hab : a ≠ b) (hvb : v ≠ b)
    (hC4 : ∀ u w, G.Adj v u → G.Adj b u → G.Adj v w → G.Adj b w → u = w) :
    ∃ S : Finset (Fin n), v ∉ S ∧ a ∉ S ∧ b ∈ S ∧
      f (input S) = false ∧ f (input (insert v S)) = true := by
  classical
  by_cases hadj : G.Adj v b
  · refine ⟨{b}, by simpa using hvb, by simpa using hab, by simp, ?_⟩
    apply off_on hf (S := {b}) _ _ hadj (by simp)
    · simpa using hbA
    · simp
  · have hw : ∃ w, G.Adj v w ∧ w ≠ a ∧ ¬ G.Adj b w := by
      by_contra! h
      by_cases hc : ∃ c, G.Adj v c ∧ G.Adj b c
      · obtain ⟨c, hvc, hbc⟩ := hc
        have hsub : G.neighborSet v ⊆ (↑({a, c} : Finset (Fin n)) : Set (Fin n)) := by
          intro w hw
          have hw' : G.Adj v w := hw
          by_cases ha : w = a
          · simp [ha]
          · have heq : w = c := hC4 w c hw' (h w hw' ha) hvc hbc
            simp [heq]
        have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
        rw [hdeg, Set.ncard_coe_finset] at hle
        have ht := Finset.card_insert_le a ({c} : Finset (Fin n))
        simp only [Finset.card_singleton] at ht
        omega
      · have hsub : G.neighborSet v ⊆ (↑({a} : Finset (Fin n)) : Set (Fin n)) := by
          intro w hw
          have hw' : G.Adj v w := hw
          by_cases heq : w = a
          · simp [heq]
          · exact (hc ⟨w, hw', h w hw' heq⟩).elim
        have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
        simp [hdeg] at hle
    obtain ⟨w, hvw, hwa, hbw⟩ := hw
    have hwA := hA w v hvw.symm
    refine ⟨{b, w}, by simp [hvb, hvw.ne], by simp [hab, Ne.symm hwa], by simp, ?_⟩
    apply off_on hf (S := {b, w}) _ _ hvw (by simp)
    · intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · exact hbA
      · exact hwA
    · intro i hi j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
      rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
      · exact fun h => G.irrefl h
      · exact hbw
      · exact fun h => hbw h.symm
      · exact fun h => G.irrefl h

def maskedBy (v : Fin n) (f : (Fin n → Bool) → Bool)
    (a b : (Fin n → Bool) → Bool) : Prop :=
  ∀ x y, (∀ i, i ≠ v → x i = y i) → a x = a y → b x = b y → f x = f y

theorem two_and_not_masked {v a b : Fin n}
    (hf : edgeSpec G A f) (hA : ∀ i j, G.Adj i j → i ∉ A)
    (hdeg : (G.neighborSet v).ncard = 3) (hva : v ≠ a) (hvb : v ≠ b) :
    ¬ maskedBy v f (fun x => x v && x a) (fun x => x v && x b) := by
  classical
  intro h
  obtain ⟨S, hv, ha, hb, hx, hy⟩ := two_and_witness (v := v) (a := a) (b := b) hf hA hdeg
  have heq := h (input S) (input (insert v S))
    (fun i hi => by simp [input, hi])
    (by simp [input, hv, ha, Ne.symm hva])
    (by simp [input, hv, hb, Ne.symm hvb])
  rw [hx, hy] at heq
  contradiction

theorem and_or_not_masked {v a b : Fin n}
    (hf : edgeSpec G A f) (hA : ∀ i j, G.Adj i j → i ∉ A)
    (hdeg : (G.neighborSet v).ncard = 3) (hbA : b ∉ A)
    (hab : a ≠ b) (hva : v ≠ a) (hvb : v ≠ b)
    (hC4 : ∀ u w, G.Adj v u → G.Adj b u → G.Adj v w → G.Adj b w → u = w) :
    ¬ maskedBy v f (fun x => x v && x a) (fun x => x v || x b) := by
  classical
  intro h
  obtain ⟨S, hv, ha, hb, hx, hy⟩ := and_or_witness hf hA hdeg hbA hab hvb hC4
  have heq := h (input S) (input (insert v S))
    (fun i hi => by simp [input, hi])
    (by simp [input, hv, ha, Ne.symm hva])
    (by simp [input, hb])
  rw [hx, hy] at heq
  contradiction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (xs : List Bool) (g : Gate) : List Bool :=
  xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)]

theorem getAppend (xs : List Bool) (v : Bool) (i : ℕ) :
    (xs ++ [v]).getD i false = if i = xs.length then v else xs.getD i false := by
  rcases lt_trichotomy i xs.length with h | h | h
  · rw [ite_eq_right h.ne, List.getD_append _ _ _ _ h]
  · subst i
    simp [List.getD_eq_getElem?_getD]
  · rw [ite_eq_right (Ne.symm h.ne)]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

def PairReader (v a b : Fin n) (op : GateOp) (g : Gate) : Prop :=
  v.val ∉ g.inputs ∨
    (g.op = .and ∧ (g.inputs = [v.val, a.val] ∨ g.inputs = [a.val, v.val])) ∨
    (g.op = op ∧ (g.inputs = [v.val, b.val] ∨ g.inputs = [b.val, v.val]))

def binary (op : GateOp) (x y : Bool) : Bool := op.eval [x, y]

theorem binary_comm (op : GateOp) (hop : op = .and ∨ op = .or) (x y : Bool) :
    binary op x y = binary op y x := by
  rcases hop with rfl | rfl <;> cases x <;> cases y <;> rfl

theorem pair_reader_agree {v a b : Fin n} {op : GateOp}
    (hop : op = .and ∨ op = .or)
    (x y : Fin n → Bool) (h₁ : binary .and (x v) (x a) = binary .and (y v) (y a))
    (h₂ : binary op (x v) (x b) = binary op (y v) (y b))
    (gs : List Gate) (readers : ∀ g ∈ gs, PairReader v a b op g)
    (xs ys : List Bool) (hLen : xs.length = ys.length) (hX : n ≤ xs.length)
    (pinsX : ∀ i : Fin n, xs.getD i.val false = x i)
    (pinsY : ∀ i : Fin n, ys.getD i.val false = y i)
    (same : ∀ i, i ≠ v.val → xs.getD i false = ys.getD i false) :
    ∀ i, i ≠ v.val → (gs.foldl step xs).getD i false = (gs.foldl step ys).getD i false := by
  induction gs generalizing xs ys with
  | nil => exact same
  | cons g gs ih =>
    have gate :
        g.op.eval (g.inputs.map fun i => xs.getD i false) =
          g.op.eval (g.inputs.map fun i => ys.getD i false) := by
      rcases readers g (by simp) with h | ⟨ho, hi | hi⟩ | ⟨ho, hi | hi⟩
      · congr 1
        exact List.map_congr_left fun i hi => same i fun he => h (he ▸ hi)
      · simpa only [ho, hi, List.map_cons, List.map_nil, pinsX, pinsY, binary] using h₁
      · simpa only [ho, hi, List.map_cons, List.map_nil, pinsX, pinsY, binary,
          binary_comm .and (Or.inl rfl) (x a) (x v),
          binary_comm .and (Or.inl rfl) (y a) (y v)] using
            (binary_comm .and (Or.inl rfl) (x a) (x v)).trans
              (h₁.trans (binary_comm .and (Or.inl rfl) (y v) (y a)))
      · simpa only [ho, hi, List.map_cons, List.map_nil, pinsX, pinsY, binary] using h₂
      · simpa only [ho, hi, List.map_cons, List.map_nil, pinsX, pinsY, binary] using
          (binary_comm op hop (x b) (x v)).trans (h₂.trans (binary_comm op hop (y v) (y b)))
    simp only [List.foldl_cons]
    apply ih (fun t ht => readers t (by simp [ht])) _ _
      (by simp [step, hLen]) (by simp [step]; omega)
    · intro i
      have h := i.isLt
      rw [step, getAppend, ite_eq_right (by omega), pinsX]
    · intro i
      have h := i.isLt
      rw [step, getAppend, ite_eq_right (by omega), pinsY]
    · intro i hi
      simp only [step, getAppend, hLen, gate, same i hi]

theorem circuit_pair_mask {v a b : Fin n} {op : GateOp} {C : Circuit}
    (hop : op = .and ∨ op = .or)
    (readers : ∀ g ∈ C.gates, PairReader v a b op g) (hOut : C.output ≠ v.val) :
    maskedBy v (circuitFun n C) (fun x => binary .and (x v) (x a))
      (fun x => binary op (x v) (x b)) := by
  intro x y same h₁ h₂
  have hs : ∀ i : ℕ, i ≠ v.val →
      (List.ofFn x).getD i false = (List.ofFn y).getD i false := by
    intro i hi
    by_cases hn : i < n
    · simp only [List.getD_eq_getElem, List.length_ofFn, hn, List.getElem_ofFn]
      exact same ⟨i, hn⟩ fun h => hi (congrArg Fin.val h)
    · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hn),
          List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hn)]
  exact pair_reader_agree hop x y h₁ h₂ C.gates readers (List.ofFn x) (List.ofFn y)
    (by simp) (by simp) (by intro i; simp) (by intro i; simp) hs C.output hOut

theorem common_unique_of_girth
    (girth : ∀ i (p : G.Walk i i), p.IsCycle → 7 ≤ p.length)
    {v b : Fin n} (hvb : v ≠ b) :
    ∀ u w, G.Adj v u → G.Adj b u → G.Adj v w → G.Adj b w → u = w := by
  intro u w hvu hbu hvw hbw
  by_contra huw
  let p : G.Walk v v := .cons hvu (.cons hbu.symm (.cons hbw (.cons hvw.symm .nil)))
  have cyc : p.IsCycle := by
    apply (SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length).2
    refine ⟨?_, by change 3 ≤ 4; decide⟩
    simp [p, SimpleGraph.Walk.isPath_def, Ne.symm hvu.ne, hbu.ne.symm, huw,
      hvb.symm, hbw.ne, hvw.ne.symm]
  have hlen := girth v p cyc
  change 7 ≤ 4 at hlen
  omega

theorem two_and_impossible {v a b : Fin n} {C : Circuit}
    (hSpec : edgeSpec G A (circuitFun n C)) (hA : ∀ i j, G.Adj i j → i ∉ A)
    (hdeg : (G.neighborSet v).ncard = 3) (hva : v ≠ a) (hvb : v ≠ b)
    (readers : ∀ g ∈ C.gates, PairReader v a b .and g) (hOut : C.output ≠ v.val) : False := by
  apply two_and_not_masked hSpec hA hdeg hva hvb
  have hm := circuit_pair_mask (Or.inl rfl) readers hOut
  simpa [binary, GateOp.eval] using hm

theorem and_or_impossible {v a b : Fin n} {C : Circuit}
    (hSpec : edgeSpec G A (circuitFun n C)) (hA : ∀ i j, G.Adj i j → i ∉ A)
    (hdeg : (G.neighborSet v).ncard = 3) (hbA : b ∉ A)
    (hab : a ≠ b) (hva : v ≠ a) (hvb : v ≠ b)
    (girth : ∀ i (p : G.Walk i i), p.IsCycle → 7 ≤ p.length)
    (readers : ∀ g ∈ C.gates, PairReader v a b .or g) (hOut : C.output ≠ v.val) : False := by
  apply and_or_not_masked hSpec hA hdeg hbA hab hva hvb (common_unique_of_girth girth hvb)
  have hm := circuit_pair_mask (Or.inr rfl) readers hOut
  simpa [binary, GateOp.eval] using hm

theorem and_or_forced_mate {v : Fin n} {S : Finset (Fin n)} {P Q : (Fin n → Bool) → Bool}
    (hf : edgeSpec G A f) (hv : v ∉ S)
    (hS : ∀ i ∈ S, i ∉ A) (hInd : ∀ i ∈ S, ∀ j ∈ S, ¬ G.Adj i j)
    (hEdge : ∃ w ∈ S, G.Adj v w)
    (mask : maskedBy v f (fun x => x v && P x) (fun x => x v || Q x)) :
    Q (input S) = true → P (input (insert v S)) = true := by
  classical
  intro hQ
  by_contra! hP
  obtain ⟨w, hw, hvw⟩ := hEdge
  obtain ⟨h0, h1⟩ := off_on hf hS hInd hvw hw
  have heq := mask (input S) (input (insert v S))
    (fun i hi => by simp [input, hi])
    (by simp [input, hv, Bool.eq_false_of_not_eq_true hP])
    (by simp [input, hv, hQ])
  rw [h0, h1] at heq
  contradiction

theorem cofactor_nonconstant {z : Fin n}
    (hf : edgeSpec G A f) (hA : ∀ i j, G.Adj i j → i ∉ A)
    (hdeg : ∀ v ∉ A, (G.neighborSet v).ncard = 3) (hz : z ∉ A) :
    ∃ x y, f (Function.update x z false) ≠ f (Function.update y z false) := by
  classical
  have hq : ∃ q, G.Adj z q := by
    by_contra! h
    have he : G.neighborSet z = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 h
    simpa [he] using hdeg z hz
  obtain ⟨q, hq⟩ := hq
  obtain ⟨S, _, hzS, _, h0, h1⟩ :=
    two_and_witness (v := q) (a := z) (b := z) hf hA (hdeg q (hA q z hq.symm))
  have hf0 : input S z = false := by simp [input, hzS]
  have hf1 : input (insert q S) z = false := by simp [input, hzS, hq.ne]
  have e0 : Function.update (input S) z false = input S := by
    rw [← hf0, Function.update_eq_self]
  have e1 : Function.update (input (insert q S)) z false = input (insert q S) := by
    rw [← hf1, Function.update_eq_self]
  exact ⟨input S, input (insert q S), by simp [e0, e1, h0, h1]⟩

end Mask5020
