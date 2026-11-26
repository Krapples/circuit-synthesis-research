import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.PermInputs
import PEqualNP.Outside.L_meta_971

namespace DeletedHeawood9748

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers.PermInputs

def edges : List (ℕ × ℕ) :=
  [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (2, 8), (2, 12), (3, 7),
   (3, 11), (3, 12), (4, 10), (4, 11), (5, 9), (5, 10), (5, 12),
   (6, 8), (6, 9), (6, 11)]

def extra : List (ℕ × ℕ) := [(1, 13), (2, 13), (4, 13)]

def evalEdges {n : ℕ} (es : List (ℕ × ℕ)) (x : Fin n → Bool) [NeZero n] : Bool :=
  es.any (fun e => x (Fin.ofNat n e.1) && x (Fin.ofNat n e.2))

theorem extra_eval (x : Fin 14 → Bool) :
    evalEdges extra x = ((x 1 || x 2 || x 4) && x 13) := by
  let a := x 1
  let b := x 2
  let c := x 4
  let d := x 13
  change (a && d || (b && d || (c && d || false))) = _
  change _ = ((a || b || c) && d)
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

theorem edge_eval_lift (x : Fin 14 → Bool) :
    evalEdges edges (x ∘ Fin.castSucc) = evalEdges edges x := by rfl

theorem step_or (W : List Bool) (a b : ℕ) :
    step W ⟨.or, [a,b]⟩ = W ++ [W.getD a false || W.getD b false] := by
  simp [step, GateOp.eval]

theorem step_and (W : List Bool) (a b : ℕ) :
    step W ⟨.and, [a,b]⟩ = W ++ [W.getD a false && W.getD b false] := by
  simp [step, GateOp.eval]

theorem snoc_value (W : List Bool) (b : Bool) :
    (W ++ [b]).getD W.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem wires_length (C : Circuit) (xs : List Bool) :
    (C.wires xs).length = xs.length + C.gates.length := by
  have aux : ∀ (gates : List Gate) (W : List Bool),
      (gates.foldl step W).length = W.length + gates.length := by
    intro gates
    induction gates with
    | nil => simp
    | cons g gs ih =>
      intro W
      simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
      omega
  exact aux C.gates xs

theorem extend_edge (C : Circuit) (hm : Monotone2 C)
    (hC : ∀ x : Fin 13 → Bool, C.eval (List.ofFn x) = evalEdges edges x) :
    ∃ D : Circuit, Monotone2 D ∧ D.size = C.size + 4 ∧
      ∀ x : Fin 14 → Bool, D.eval (List.ofFn x) = evalEdges (edges ++ extra) x := by
  let P := relabel 13 14 Fin.castSucc C
  let m := 14 + P.gates.length
  let g₀ : Gate := ⟨.or, [1, 2]⟩
  let g₁ : Gate := ⟨.or, [m, 4]⟩
  let g₂ : Gate := ⟨.and, [m+1, 13]⟩
  let g₃ : Gate := ⟨.or, [P.output, m+2]⟩
  let D : Circuit := ⟨P.gates ++ [g₀,g₁,g₂,g₃], m+3⟩
  have keep (x : Fin 14 → Bool) : P.eval (List.ofFn x) = C.eval (List.ofFn (x ∘ Fin.castSucc)) :=
    (rel_fold 13 14 Fin.castSucc C.gates _ _ (rel_init 13 14 Fin.castSucc x)).2.2 C.output
  have hPlt : P.output < m := by
    by_contra! h
    let x : Fin 14 → Bool := fun _ => true
    have hx : (P.wires (List.ofFn x)).length ≤ P.output := by
      rwa [wires_length, List.length_ofFn]
    have hf : P.eval (List.ofFn x) = false := List.getD_eq_default _ _ hx
    rw [keep, hC] at hf
    contradiction
  refine ⟨D, ?_, by simp [D, Circuit.size, P, relabel], ?_⟩
  · intro g hg
    change g ∈ P.gates ++ [g₀,g₁,g₂,g₃] at hg
    rcases List.mem_append.mp hg with hold | hnew
    · obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hold
      exact ⟨(hm g' hg').1, by simpa [relGate] using (hm g' hg').2⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hnew
      rcases hnew with rfl | rfl | rfl | rfl
      · exact ⟨Or.inr rfl, Nat.le_refl 2⟩
      · exact ⟨Or.inr rfl, Nat.le_refl 2⟩
      · exact ⟨Or.inl rfl, Nat.le_refl 2⟩
      · exact ⟨Or.inr rfl, Nat.le_refl 2⟩
  · intro x
    let W := P.wires (List.ofFn x)
    let a := x 1 || x 2
    let b := a || x 4
    let c := b && x 13
    have len : W.length = m := by simp [W, m, wires_length]
    have raw (i : Fin 14) : W.getD i.val false = x i := by
      have kept : ∀ (gs : List Gate) (xs : List Bool) (j : ℕ), j < xs.length →
          (gs.foldl step xs).getD j false = xs.getD j false := by
        intro gs
        induction gs with
        | nil => simp
        | cons g gs ih =>
          intro xs j hj
          rw [List.foldl_cons, ih _ _ (by simp [step]; omega)]
          exact List.getD_append _ _ _ _ hj
      change (P.gates.foldl step (List.ofFn x)).getD i.val false = x i
      rw [kept _ _ _ (by simp)]
      rw [List.getD_eq_getElem _ _ (by simp)]
      exact List.getElem_ofFn _
    have raw₁ : W.getD 1 false = x 1 := raw (1 : Fin 14)
    have raw₂ : W.getD 2 false = x 2 := raw (2 : Fin 14)
    have raw₄ : W.getD 4 false = x 4 := raw (4 : Fin 14)
    have raw₁₃ : W.getD 13 false = x 13 := raw (13 : Fin 14)
    have e₀ : step W g₀ = W ++ [a] := by
      simp only [g₀, step_or]
      rw [raw₁, raw₂]
    have e₁ : step (W ++ [a]) g₁ = (W ++ [a]) ++ [b] := by
      simp only [g₁, step_or]
      rw [← len, snoc_value, List.getD_append _ _ _ _ (by omega), raw₄]
    have e₂ : step ((W ++ [a]) ++ [b]) g₂ = ((W ++ [a]) ++ [b]) ++ [c] := by
      have len₁ : (W ++ [a]).length = m + 1 := by simp [len]
      simp only [g₂, step_and]
      rw [← len₁, snoc_value, List.getD_append _ _ _ _ (by omega),
        List.getD_append _ _ _ _ (by omega), raw₁₃]
    have e₃ : step (((W ++ [a]) ++ [b]) ++ [c]) g₃ =
        (((W ++ [a]) ++ [b]) ++ [c]) ++ [W.getD P.output false || c] := by
      have len₂ : ((W ++ [a]) ++ [b]).length = m + 2 := by simp [len]
      have len₁ : (W ++ [a]).length = m + 1 := by simp [len]
      simp only [g₃, step_or]
      rw [← len₂, snoc_value, List.getD_append _ _ _ _ (by omega),
        List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
    change ((P.gates ++ [g₀,g₁,g₂,g₃]).foldl step (List.ofFn x)).getD (m+3) false = _
    rw [List.foldl_append]
    change (step (step (step (step W g₀) g₁) g₂) g₃).getD (m+3) false = _
    rw [e₀, e₁, e₂, e₃]
    have len₃ : (((W ++ [a]) ++ [b]) ++ [c]).length = m + 3 := by simp [len]
    rw [← len₃, snoc_value]
    change (P.eval (List.ofFn x) || c) = _
    rw [keep, hC, edge_eval_lift]
    have combine : evalEdges (edges ++ extra) x = (evalEdges edges x || evalEdges extra x) := by
      exact List.any_append
    rw [combine, extra_eval]

def official : List (ℕ × ℕ) :=
  [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8),
   (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11),
   (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]

theorem official_mem (u v : ℕ) : (u,v) ∈ edges ++ extra ↔ (u,v) ∈ official := by
  simp only [edges, extra, official, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false]
  tauto

theorem heawood_test (x : Fin 14 → Bool) :
    evalEdges (edges ++ extra) x = true ↔
      ∃ u v : Fin 14, (u.val, v.val) ∈ official ∧ x u = true ∧ x v = true := by
  rw [evalEdges, List.any_eq_true]
  constructor
  · rintro ⟨⟨a,b⟩, h, hval⟩
    have bounded : (edges ++ extra).all (fun e => decide (e.1 < 14 ∧ e.2 < 14)) = true := by decide
    obtain ⟨ha, hb⟩ := of_decide_eq_true ((List.all_eq_true.1 bounded) (a,b) h)
    exact ⟨⟨a,ha⟩, ⟨b,hb⟩, (official_mem a b).mp h, by
      simpa [Fin.ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using hval⟩
  · rintro ⟨u,v,h,hu,hv⟩
    exact ⟨(u.val,v.val), (official_mem _ _).mpr h, by simp [hu, hv]⟩

theorem lower_mono
    (C : Circuit) (hm : Monotone2 C)
    (hC : ∀ x : Fin 13 → Bool, C.eval (List.ofFn x) = evalEdges edges x) :
    23 ≤ C.size := by
  obtain ⟨D, hD, hs, hEval⟩ := extend_edge C hm hC
  have bound := PEqualNP.Outside.L_meta_971 D hD (fun x => by
    rw [hEval x, heawood_test]
    rfl)
  omega

theorem counted_not_required (C : Circuit) (ok : FanInTwo C) (hs : C.size ≤ 22)
    (hC : ∀ x : Fin 13 → Bool, C.eval (List.ofFn x) = evalEdges edges x) :
    ∃ g ∈ C.gates, g.op = .not := by
  classical
  by_contra! h
  have hm : Monotone2 C := by
    intro g hg
    obtain ⟨allowed, cap⟩ := ok g hg
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at allowed
    exact ⟨allowed.elim Or.inl (fun h₁ => h₁.elim Or.inr (fun e => (h g hg e).elim)), cap⟩
  have lb := lower_mono C hm hC
  omega

end DeletedHeawood9748
