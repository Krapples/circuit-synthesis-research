import PEqualNP.Outside.L_meta_8029

namespace Guard7893

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.Outside.L_meta_8029 (wire_mono)

abbrev row (k : ℕ) (i : Fin 10) : Bool := k.testBit i.val
abbrev padding : List ℕ := [50,104,116,138,208,276,402,548,554,770]
abbrev links : List (Fin 10 × Fin 10) :=
  [(1,2),(2,3),(3,4),(1,6),(2,7),(5,7),(3,8),(5,8),(6,8),(4,9),(6,9),(7,9)]
def neighbour (x : Fin 10 → Bool) : Bool := x 1 || x 4 || x 5
def withoutZero (x : Fin 10 → Bool) : Bool := links.any fun e => x e.1 && x e.2
def target (x : Fin 10 → Bool) : Bool := withoutZero x || (x 0 && neighbour x)
def guard (B : Circuit) (w : ℕ) (x : Fin 10 → Bool) : Bool :=
  (B.wires (List.ofFn (Function.update x 0 false))).getD w false

theorem upWire (B : Circuit) (mono : Monotone2 B) {x y : Fin 10 → Bool}
    (sub : ∀ i, x i = true → y i = true) (w : ℕ) :
    (B.wires (List.ofFn x)).getD w false = true →
      (B.wires (List.ofFn y)).getD w false = true := by
  apply wire_mono B mono _ _ (by simp) _ w
  intro k hk
  by_cases h : k < 10
  · rw [List.getD_eq_getElem _ _ (by simpa using h)] at hk ⊢
    simp only [List.getElem_ofFn] at hk ⊢
    exact sub ⟨k,h⟩ hk
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt h)] at hk
    cases hk

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 10000 in
theorem independentMask :
    ∀ x : Fin 10 → Bool, x 0 = false → withoutZero x = false →
      (∃ k ∈ padding, ∀ i, x i = true → row k i = true) ∨ x = row 200 ∨ x = row 772 := by
  decide +kernel

theorem oneGateGuard :
    ∀ (isOr : Bool) (a b : Fin 10), a ≠ 0 → b ≠ 0 →
      padding.all (fun k => !(if isOr then row k a || row k b else row k a && row k b)) = true →
      isOr = false ∧ ((a,b) ∈ links ∨ (b,a) ∈ links) := by
  intro isOr
  cases isOr <;> decide +kernel

theorem independentGuard (B : Circuit) (mono : Monotone2 B) (w : ℕ)
    (zero : ∀ k ∈ padding, guard B w (row k) = false)
    {x : Fin 10 → Bool} (h : withoutZero x = false) (on : guard B w x = true) :
    Function.update x 0 false = row 200 ∨ Function.update x 0 false = row 772 := by
  let y := Function.update x 0 false
  have drop : withoutZero y = withoutZero x := by simp [withoutZero,y,links]
  rcases independentMask y (by simp [y]) (drop.trans h) with ⟨k, hk, sub⟩ | alt
  · have off : row k 0 = false := by
      have table : ∀ k ∈ padding, row k 0 = false := by decide +kernel
      exact table k hk
    have same : Function.update (row k) 0 false = row k := by
      rw [← off]
      exact Function.update_eq_self _ _
    have on' := upWire B mono sub w on
    have zero' := zero k hk
    rw [guard,same] at zero'
    exact (Bool.false_ne_true (zero'.symm.trans on')).elim
  · exact alt

theorem guardInternal (B : Circuit) (w : ℕ) (nonzero : w ≠ 0)
    (zero : ∀ k ∈ padding, guard B w (row k) = false) : 10 ≤ w := by
  by_contra! bound
  let i : Fin 10 := ⟨w,bound⟩
  have table : ∀ i : Fin 10, i ≠ 0 → ∃ k ∈ padding, row k i = true := by decide +kernel
  obtain ⟨k,hk,on⟩ := table i (by intro e; exact nonzero (congrArg Fin.val e))
  have hval : (Function.update (row k) 0 false) i = true := by
    rw [Function.update_of_ne (by intro e; exact nonzero (congrArg Fin.val e))]
    exact on
  have preserve : ∀ (gs : List Gate) (ys : List Bool), w < ys.length →
      (gs.foldl (fun zs g => zs ++ [g.op.eval (g.inputs.map fun j => zs.getD j false)]) ys).getD w false =
        ys.getD w false := by
    intro gs
    induction gs with
    | nil => simp
    | cons g gs ih =>
      intro ys hw
      rw [List.foldl_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]
  have z := zero k hk
  unfold guard Circuit.wires at z
  rw [preserve _ _ (by simpa using bound)] at z
  rw [List.getD_eq_getElem _ _ (by simpa using bound)] at z
  simp only [List.getElem_ofFn] at z
  exact Bool.false_ne_true (z.symm.trans hval)

theorem basePlusGuardedEdges (B : Circuit) (mono : Monotone2 B) (w : ℕ)
    (zero : ∀ k ∈ padding, guard B w (row k) = false)
    (sim : ∀ x : Fin 10 → Bool,
      circuitFun 10 B (Function.update x 0 (x 0 || guard B w x)) = target x)
    (x : Fin 10 → Bool) :
    (circuitFun 10 B x || (guard B w x && withoutZero x)) = target x := by
  cases h : guard B w x
  · have same := sim x
    simpa [h, Function.update_eq_self] using same
  cases hH : withoutZero x
  · have same : neighbour (Function.update x 0 false) = neighbour x := by simp [neighbour]
    have alt := independentGuard B mono w zero hH h
    have hn : neighbour x = false := by
      rw [← same]
      rcases alt with alt | alt <;> rw [alt] <;> decide
    have hf : target x = false := by simp [target, hH, hn]
    have monotoneInput : ∀ i, x i = true → (Function.update x 0 (x 0 || guard B w x)) i = true := by
      intro i hi
      by_cases eq : i = 0
      · subst i; simp [hi]
      · simpa [Function.update_of_ne eq] using hi
    have baseOff : circuitFun 10 B x = false := by
      cases hb : circuitFun 10 B x
      · rfl
      · have on := upWire B mono monotoneInput B.output hb
        have off := sim x
        rw [hf] at off
        exact (Bool.false_ne_true (off.symm.trans on)).elim
    simp [hf, baseOff]
  · simp [target, hH]

end Guard7893

#print axioms Guard7893.independentGuard
#print axioms Guard7893.guardInternal
#print axioms Guard7893.basePlusGuardedEdges
#print axioms Guard7893.oneGateGuard
