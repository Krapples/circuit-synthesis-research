import Mathlib
import PEqualNP.Defs

-- Wire-evaluation and bypass helpers reproduced from open-goat/pequalnp-proofs,
-- pinned revision 3db0136bf094e975baaf20214b01e4b4579059f2,
-- lean/PEqualNP/Outside/L_meta_2668.lean (PR #4874), Apache-2.0.
-- That file credits willakone, L-meta-1499, PR #3112 for bypass helpers.
-- New exact-AO2 and minimality results begin after the imported helper block.

namespace ResearchVerification.OneJunkErase

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CircuitMoves

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt2 (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt2 gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt2 gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt2 _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

lemma opMono_eq : OpMono Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

lemma opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [ite_eq_right hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [ite_eq_left hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h'; exact ⟨hlt, h'⟩
    · rw [ite_eq_right hlt] at h'; cases h'
  · intro h i hi
    rw [ite_eq_left (h i hi).1]; exact (h i hi).2

lemma val_prefix {n : ℕ} {C D : Circuit} {x : List Bool} (hx : x.length = n) {m : ℕ}
    (hmC : m ≤ C.gates.length) (hmD : m ≤ D.gates.length)
    (hg : ∀ k < m, gateAt D k = gateAt C k) : ∀ u, u < n + m → val D x u = val C x u := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu
    by_cases hun : u < n
    · rw [val_input hx hun, val_input hx hun]
    · obtain ⟨k, rfl⟩ : ∃ k, u = n + k := ⟨u - n, by omega⟩
      have hk : k < m := by omega
      rw [val_gate hx (by omega), val_gate hx (by omega), hg k hk]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < n + k
      · rw [ite_eq_left hi, ite_eq_left hi]; exact ih i hi (by omega)
      · rw [ite_eq_right hi, ite_eq_right hi]

def aliasWire (w i u : ℕ) : ℕ := if u = w then i else if w < u then u - 1 else u

def aliasGate (w i : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (aliasWire w i)⟩

def bypass (n : ℕ) (C : Circuit) (r i : ℕ) : Circuit :=
  ⟨(List.range (C.gates.length - 1)).map (fun k =>
      if k < r then gateAt C k else aliasGate (n + r) i (gateAt C (k + 1))),
    aliasWire (n + r) i C.output⟩

lemma bypass_length (n : ℕ) (C : Circuit) (r i : ℕ) :
    (bypass n C r i).gates.length = C.gates.length - 1 := by simp [bypass]

lemma bypass_output (n : ℕ) (C : Circuit) (r i : ℕ) :
    (bypass n C r i).output = aliasWire (n + r) i C.output := rfl

lemma gateAt_bypass {n : ℕ} {C : Circuit} {r i k : ℕ} (hk : k < C.gates.length - 1) :
    gateAt (bypass n C r i) k =
      if k < r then gateAt C k else aliasGate (n + r) i (gateAt C (k + 1)) := by
  have hk' : k < (bypass n C r i).gates.length := by rw [bypass_length]; exact hk
  rw [gateAt_eq hk']
  simp [bypass]

lemma bypass_val_lt {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r i : ℕ}
    (hr : r < C.gates.length) : ∀ u, u < n + r → val (bypass n C r i) x u = val C x u := by
  apply val_prefix hx (by omega) (by rw [bypass_length]; omega)
  intro k hk
  rw [gateAt_bypass (by omega), ite_eq_left hk]

lemma aliasWire_self (w i : ℕ) : aliasWire w i w = i := by simp [aliasWire]

lemma aliasWire_lt_self {w i u : ℕ} (hu : u < w) : aliasWire w i u = u := by
  unfold aliasWire; rw [ite_eq_right (by omega), ite_eq_right (by omega)]

lemma aliasWire_gt_self {w i u : ℕ} (hu : w < u) : aliasWire w i u = u - 1 := by
  unfold aliasWire; rw [ite_eq_right (by omega), ite_eq_left hu]

lemma bypass_rel {R : Bool → Bool → Prop} (hrefl : ∀ b, R b b) (hmono : OpMono R)
    {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hR : (∃ k, r < k ∧ k < C.gates.length ∧ n + r ∈ (gateAt C k).inputs) →
      R (val C x (n + r)) (val C x i)) :
    ∀ u, u ≠ n + r → R (val C x u) (val (bypass n C r i) x (aliasWire (n + r) i u)) := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hne
    by_cases hlt : u < n + r
    · rw [aliasWire_lt_self hlt, bypass_val_lt hx hr u hlt]; exact hrefl _
    · rw [aliasWire_gt_self (by omega)]
      by_cases hge : n + C.gates.length ≤ u
      · rw [val_ge hx hge, val_ge hx (by rw [bypass_length]; omega)]; exact hrefl _
      · obtain ⟨k, rfl⟩ : ∃ k, u = n + (k + 1) := ⟨u - n - 1, by omega⟩
        have hk1 : k + 1 < C.gates.length := by omega
        have hkr : ¬ k < r := by omega
        have e : n + (k + 1) - 1 = n + k := by omega
        rw [e, val_gate hx hk1, val_gate hx (by rw [bypass_length]; omega),
          gateAt_bypass (by omega), ite_eq_right hkr]
        simp only [aliasGate, List.map_map]
        refine hmono _ (hAO _ hk1) _ _ _ ?_
        intro i' hi'
        simp only [Function.comp_apply]
        by_cases h1 : i' = n + r
        · subst h1
          rw [aliasWire_self, ite_eq_left (by omega)]
          have hgi : (if i < n + k then val (bypass n C r i) x i else false) = val C x i := by
            rcases hi with hi | hi
            · rw [ite_eq_left (by omega), bypass_val_lt hx hr i hi]
            · rw [ite_eq_right (by omega), val_ge hx hi]
          rw [hgi]
          exact hR ⟨k + 1, by omega, hk1, hi'⟩
        · by_cases h2 : i' < n + r
          · rw [aliasWire_lt_self h2, ite_eq_left (by omega), ite_eq_left (by omega),
              bypass_val_lt hx hr i' h2]
            exact hrefl _
          · by_cases h3 : i' < n + (k + 1)
            · have key := ih i' h3 h1
              rw [aliasWire_gt_self (by omega)] at key
              rw [aliasWire_gt_self (by omega), ite_eq_left h3, ite_eq_left (by omega)]
              exact key
            · rw [aliasWire_gt_self (by omega), ite_eq_right h3, ite_eq_right (by omega)]
              exact hrefl _

lemma bypass_eval_rel {R : Bool → Bool → Prop} (hrefl : ∀ b, R b b) (hmono : OpMono R)
    {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hR : R (val C x (n + r)) (val C x i)) :
    R (C.eval x) ((bypass n C r i).eval x) := by
  rw [eval_eq_val, eval_eq_val, bypass_output]
  by_cases h : C.output = n + r
  · have hgi : val (bypass n C r i) x i = val C x i := by
      rcases hi with hi | hi
      · exact bypass_val_lt hx hr i hi
      · rw [val_ge hx hi, val_ge hx (by rw [bypass_length]; omega)]
    rw [h, aliasWire_self, hgi]; exact hR
  · exact bypass_rel hrefl hmono hx hAO hr hi (fun _ => hR) _ h

lemma bypass_eval_eq {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hR : val C x (n + r) = val C x i) :
    (bypass n C r i).eval x = C.eval x :=
  (bypass_eval_rel (R := Eq) (fun _ => rfl) opMono_eq hx hAO hr hi hR).symm

lemma bypass_eval_unread {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hout : C.output ≠ n + r)
    (hno : ∀ k, r < k → k < C.gates.length → n + r ∉ (gateAt C k).inputs) :
    (bypass n C r i).eval x = C.eval x := by
  rw [eval_eq_val, eval_eq_val, bypass_output]
  exact (bypass_rel (R := Eq) (fun _ => rfl) opMono_eq hx hAO hr hi
    (fun ⟨k, hrk, hk, hm⟩ => absurd hm (hno k hrk hk)) _ hout).symm

lemma bypass_AO {n : ℕ} {C : Circuit} {r i : ℕ} (hr : r < C.gates.length)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) :
    ∀ k < (bypass n C r i).gates.length,
      (gateAt (bypass n C r i) k).op = GateOp.and ∨
        (gateAt (bypass n C r i) k).op = GateOp.or := by
  intro k hk
  rw [bypass_length] at hk
  rw [gateAt_bypass hk]
  split_ifs with h
  · exact hAO k (by omega)
  · exact hAO (k + 1) (by omega)

lemma bypass_mem {n : ℕ} {C : Circuit} {r i : ℕ} :
    ∀ g ∈ (bypass n C r i).gates, ∃ g' ∈ C.gates, g.op = g'.op ∧
      g.inputs.length = g'.inputs.length := by
  intro g hg
  simp only [bypass, List.mem_map, List.mem_range] at hg
  obtain ⟨k, hk, rfl⟩ := hg
  split_ifs with h
  · exact ⟨gateAt C k, gateAt_mem (by omega), rfl, rfl⟩
  · exact ⟨gateAt C (k + 1), gateAt_mem (by omega), rfl, by simp [aliasGate]⟩

lemma aliasWire_lt {w i u m : ℕ} (hi : i < w) (hwm : w ≤ m) (hu : u < m + 1) :
    aliasWire w i u < m := by
  unfold aliasWire; split_ifs <;> omega

lemma bypass_readsBack {n : ℕ} {C : Circuit} {r i : ℕ} (hi : i < n + r)
    (hRB : ∀ k < C.gates.length, ∀ u ∈ (gateAt C k).inputs, u < n + k) :
    ∀ k < (bypass n C r i).gates.length,
      ∀ u ∈ (gateAt (bypass n C r i) k).inputs, u < n + k := by
  intro k hk u hu
  rw [bypass_length] at hk
  rw [gateAt_bypass hk] at hu
  split_ifs at hu with h
  · exact hRB k (by omega) u hu
  · simp only [aliasGate, List.mem_map] at hu
    obtain ⟨u', hu', rfl⟩ := hu
    have := hRB (k + 1) (by omega) u' hu'
    exact aliasWire_lt hi (by omega) (by omega)


lemma erase_eq_bypass (n : ℕ) (C : Circuit) (r i : ℕ) (hr : r < C.gates.length) :
    PEqualNP.CircuitMoves.eraseGate n C r i = bypass n C r i := by
  unfold PEqualNP.CircuitMoves.eraseGate
  rw [ite_eq_left hr]
  change Circuit.mk _ (aliasWire (n + r) i C.output) = Circuit.mk _ (aliasWire (n + r) i C.output)
  congr 1
  apply List.ext_getElem
  · simp; omega
  · intro k hk hk'
    have hlen : (C.gates.take r).length = r := by simp; omega
    have hklen : k < C.gates.length - 1 := by simpa [bypass] using hk'
    simp only [List.getElem_map, List.getElem_range]
    by_cases hkr : k < r
    · rw [ite_eq_left hkr, List.getElem_append_left (by omega), List.getElem_take,
        gateAt_eq (by omega)]
    · rw [ite_eq_right hkr, List.getElem_append_right (by omega), List.getElem_map,
        List.getElem_drop]
      simp only [hlen]
      have he : r + 1 + (k - r) = k + 1 := by omega
      simp only [he]
      rw [gateAt_eq (by omega : k + 1 < C.gates.length)]
      rfl

lemma mono_ops {C : Circuit} (hM : Monotone2 C) :
    ∀ k < C.gates.length, (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or := by
  intro k hk
  exact (hM _ (gateAt_mem hk)).1

lemma wire_monotone (n : ℕ) (C : Circuit) (hM : Monotone2 C) (x y : Fin n → Bool)
    (hxy : ∀ i, x i = true → y i = true) :
    ∀ u, val C (List.ofFn x) u = true → val C (List.ofFn y) u = true := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    by_cases hun : u < n
    · rw [val_input (n := n) (by simp) hun, val_input (n := n) (by simp) hun]
      simpa [hun] using hxy ⟨u, hun⟩
    · by_cases hge : n + C.gates.length ≤ u
      · rw [val_ge (n := n) (by simp) hge]
        intro h; cases h
      · obtain ⟨k, rfl⟩ : ∃ k, u = n + k := ⟨u - n, by omega⟩
        have hk : k < C.gates.length := by omega
        rw [val_gate (n := n) (by simp) hk, val_gate (n := n) (by simp) hk]
        apply opMono_imp _ (mono_ops hM k hk)
        intro i hi
        by_cases hil : i < n + k
        · rw [ite_eq_left hil, ite_eq_left hil]
          exact ih i hil
        · rw [ite_eq_right hil, ite_eq_right hil]
          exact id

lemma circuit_monotone (n : ℕ) (C : Circuit) (hM : Monotone2 C) (x y : Fin n → Bool)
    (hxy : ∀ i, x i = true → y i = true) : C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true :=
  wire_monotone n C hM x y hxy C.output

lemma opMono_reverse : OpMono (fun a b => b = true → a = true) := by
  intro op hop l f g h
  exact opMono_imp op hop l g f h

lemma bypass_mono {n : ℕ} {C : Circuit} {r i : ℕ} (hM : Monotone2 C) :
    Monotone2 (bypass n C r i) := by
  intro g hg
  obtain ⟨g', hg', hop, hlen⟩ := bypass_mem g hg
  rw [hop, hlen]
  exact hM g' hg'

lemma graph_true {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ p l, G.Adj p l ∧ x p = true ∧ x l = true := by
  simp [graphFun]

lemma pair_true {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (p l : Fin n)
    (hp : G.Adj p l) : graphFun G ∅ (PEqualNP.EdgeOwnership.pairInput p l) = true := by
  rw [graph_true]
  exact ⟨p, l, hp, by simp [PEqualNP.EdgeOwnership.pairInput], by simp [PEqualNP.EdgeOwnership.pairInput]⟩

-- New results: specialize actual upstream erasure to exact binary AO circuits.

lemma ao_mono {n : ℕ} {C : Circuit} (h : IsAO2 n C) : Monotone2 C := by
  intro g hg
  exact ⟨h.1 g hg, (h.2.2 g hg).le⟩

lemma erase_exactAO {n : ℕ} {C : Circuit} {r i : ℕ}
    (h : IsAO2 n C) (hr : r < C.gates.length) (hi : i < n + r) :
    IsAO2 n (eraseGate n C r i) := by
  rw [erase_eq_bypass n C r i hr]
  refine ⟨?_, bypass_readsBack hi h.2.1, ?_⟩
  · intro g hg
    obtain ⟨g', hg', hop, _⟩ := bypass_mem g hg
    rw [hop]
    exact h.1 g' hg'
  · intro g hg
    obtain ⟨g', hg', _, hlen⟩ := bypass_mem g hg
    rw [hlen]
    exact h.2.2 g' hg'

lemma erase_exactSize {n : ℕ} {C : Circuit} {r i : ℕ}
    (hr : r < C.gates.length) :
    (eraseGate n C r i).size = C.size - 1 := by
  rw [erase_eq_bypass n C r i hr]
  exact bypass_length n C r i

/-- An earlier equal-valued wire makes a counted gate redundant. -/
theorem noEqualEarlier {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (h : IsLeastAO G C)
    (r i : ℕ) (hr : r < C.gates.length) (hi : i < n + r) :
    ¬ (∀ x : Fin n → Bool,
      val C (List.ofFn x) (n + r) = val C (List.ofFn x) i) := by
  intro he
  let D := eraseGate n C r i
  have hD : IsAO2 n D := erase_exactAO h.1 hr hi
  have hf : circuitFun n D = circuitFun n C := by
    funext x
    change D.eval (List.ofFn x) = C.eval (List.ofFn x)
    dsimp [D]
    rw [erase_eq_bypass n C r i hr]
    exact bypass_eval_eq (n := n) (by simp) (mono_ops (ao_mono h.1)) hr
      (Or.inl hi) (he x)
  have hb := h.2.2 D hD (hf.trans h.2.1)
  have hs : D.size = C.size - 1 := erase_exactSize hr
  change r < C.size at hr
  omega

/-- A gate that never reaches the output through any immediate reader
    can be deleted. The redirect wire must be earlier, not a false wire. -/
theorem noUnreadGate {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (h : IsLeastAO G C)
    (r i : ℕ) (hr : r < C.gates.length) (hi : i < n + r)
    (hout : C.output ≠ n + r) :
    ∃ k, r < k ∧ k < C.gates.length ∧ n + r ∈ (gateAt C k).inputs := by
  by_contra hn
  have hno : ∀ k, r < k → k < C.gates.length → n + r ∉ (gateAt C k).inputs := by
    intro k hrk hk hm
    exact hn ⟨k, hrk, hk, hm⟩
  let D := eraseGate n C r i
  have hD : IsAO2 n D := erase_exactAO h.1 hr hi
  have hf : circuitFun n D = circuitFun n C := by
    funext x
    change D.eval (List.ofFn x) = C.eval (List.ofFn x)
    dsimp [D]
    rw [erase_eq_bypass n C r i hr]
    exact bypass_eval_unread (n := n) (by simp) (mono_ops (ao_mono h.1)) hr
      (Or.inl hi) hout hno
  have hb := h.2.2 D hD (hf.trans h.2.1)
  have hs : D.size = C.size - 1 := erase_exactSize hr
  change r < C.size at hr
  omega

/-- Concrete strict deletion of an AND reading a clean operand. The
    replacement is an actual earlier wire, and the output is preserved
    on every input, not merely on the graph's positive edge pairs. -/
theorem noCleanAndOperand {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (h : IsLeastAO G C)
    (r i : ℕ) (hr : r < C.gates.length) (hi : i ∈ (gateAt C r).inputs)
    (hand : (gateAt C r).op = GateOp.and) :
    ¬ (∀ x : Fin n → Bool, val C (List.ofFn x) i = true →
      graphFun G ∅ x = true) := by
  intro hclean
  have hib := h.1.2.1 r hr i hi
  let D := eraseGate n C r i
  have hD : IsAO2 n D := erase_exactAO h.1 hr hib
  have hf : circuitFun n D = graphFun G ∅ := by
    funext x
    have hle : val C (List.ofFn x) (n + r) = true →
        val C (List.ofFn x) i = true := by
      intro hv
      exact ((val_and (n := n) (by simp) hr hand).mp hv i hi).2
    have hpos : C.eval (List.ofFn x) = true → D.eval (List.ofFn x) = true := by
      dsimp [D]
      rw [erase_eq_bypass n C r i hr]
      exact bypass_eval_rel (R := fun a b => a = true → b = true)
        (fun _ => id) opMono_imp (n := n) (by simp)
        (mono_ops (ao_mono h.1)) hr (Or.inl hib) hle
    have hC : C.eval (List.ofFn x) = graphFun G ∅ x := congrFun h.2.1 x
    change D.eval (List.ofFn x) = graphFun G ∅ x
    cases hx : graphFun G ∅ x with
    | false =>
        have hz : val C (List.ofFn x) i = false := by
          cases hv : val C (List.ofFn x) i with
          | false => rfl
          | true =>
              have hh := hclean x hv
              rw [hx] at hh
              cases hh
        have he : val C (List.ofFn x) (n + r) = val C (List.ofFn x) i := by
          rw [hz]
          cases hv : val C (List.ofFn x) (n + r) with
          | false => rfl
          | true =>
              have hh := hle hv
              rw [hz] at hh
              cases hh
        change (eraseGate n C r i).eval (List.ofFn x) = false
        rw [erase_eq_bypass n C r i hr,
          bypass_eval_eq (n := n) (by simp) (mono_ops (ao_mono h.1)) hr
            (Or.inl hib) he, hC, hx]
    | true =>
        exact hpos (hC.trans hx)
  have hb := h.2.2 D hD hf
  have hs : D.size = C.size - 1 := erase_exactSize hr
  change r < C.size at hr
  omega

#print axioms erase_exactAO
#print axioms erase_exactSize
#print axioms noEqualEarlier
#print axioms noUnreadGate
#print axioms noCleanAndOperand


-- Structural consequences of exact AO2 minimality.

open PEqualNP.EdgeOwnership PEqualNP.Core PEqualNP.ReadTwo

lemma twoOperands {n : ℕ} {C : Circuit} (h : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) :
    ∃ a b : ℕ, (gateAt C j).inputs = [a, b] := by
  have hl := h.2.2 _ (gateAt_mem hj)
  generalize he : (gateAt C j).inputs = L at hl ⊢
  cases L with
  | nil => simp at hl
  | cons a L =>
    cases L with
    | nil => simp at hl
    | cons b L =>
      cases L with
      | nil => exact ⟨a, b, rfl⟩
      | cons c L => simp at hl

/-- Every existing wire is true at the all-true input. No constants
    or invalid reads are permitted in IsAO2. -/
theorem allTrueWires {n : ℕ} {C : Circuit} (h : IsAO2 n C) :
    ∀ w < n + C.gates.length, val C (List.ofFn (fun _ : Fin n => true)) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hin : w < n
    · rw [val_input (n := n) (by simp) hin]
      simp [List.getD_eq_getElem?_getD, hin]
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < C.gates.length := by omega
      rcases h.1 _ (gateAt_mem hj) with hand | hor
      · apply (val_and (n := n) (by simp) hj hand).mpr
        intro i hi
        have hlt := h.2.1 j hj i hi
        exact ⟨hlt, ih i hlt (by omega)⟩
      · obtain ⟨a, b, hab⟩ := twoOperands h hj
        have ha : a ∈ (gateAt C j).inputs := by rw [hab]; simp
        have hlt := h.2.1 j hj a ha
        exact (val_or (n := n) (by simp) hj hor).mpr
          ⟨a, ha, hlt, ih a hlt (by omega)⟩

/-- A raw wire is not below the graph function: a singleton is never an edge. -/
theorem rawNotClean {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (a : Fin n) :
    ¬ (∀ x : Fin n → Bool, val C (List.ofFn x) a.val = true →
      graphFun G ∅ x = true) := by
  intro h
  let x : Fin n → Bool := fun v => decide (v = a)
  have hv : val C (List.ofFn x) a.val = true := by
    rw [val_input (n := n) (by simp) a.isLt]
    simp [List.getD_eq_getElem?_getD, a.isLt, x]
  obtain ⟨p, q, hpq, hp, hq⟩ := (graph_true G x).mp (h x hv)
  have he1 : p = a := by simpa [x] using hp
  have he2 : q = a := by simpa [x] using hq
  exact G.ne_of_adj hpq (he1.trans he2.symm)

/-- Repeated operands would make a gate equal to an earlier wire. -/
theorem distinctOperands {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) {j a : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).inputs ≠ [a, a] := by
  intro he
  have ha : a ∈ (gateAt C j).inputs := by rw [he]; simp
  have hlt := h.1.2.1 j hj a ha
  apply noEqualEarlier G C h j a hj hlt
  intro x
  rcases h.1.1 _ (gateAt_mem hj) with hand | hor
  · rw [val_gate (n := n) (by simp) hj, hand, he]
    simp [GateOp.eval, hlt]
  · rw [val_gate (n := n) (by simp) hj, hor, he]
    simp [GateOp.eval, hlt]

/-- If a least circuit has any gate at all, its last gate is the output.
    In particular, an invalid output wire is impossible in this case. -/
theorem outputLast {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hpos : 0 < C.gates.length) :
    C.output = n + (C.gates.length - 1) := by
  let j := C.gates.length - 1
  have hj : j < C.gates.length := by dsimp [j]; omega
  obtain ⟨a, b, hab⟩ := twoOperands h.1 hj
  have ha := h.1.2.1 j hj a (by rw [hab]; simp)
  by_contra hn
  obtain ⟨k, hjk, hk, _⟩ := noUnreadGate G C h j a hj ha hn
  dsimp [j] at hjk
  omega

/-- Empty graph has a zero-gate circuit with a missing output wire.
    This handles the degenerate case allowed by the actual definitions. -/
theorem emptyGraphNoGates {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (he : ∀ a b, ¬ G.Adj a b) :
    C.gates.length = 0 := by
  let D : Circuit := ⟨[], n⟩
  have hao : IsAO2 n D := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      simp [D] at hg
    · intro j hj
      simp [D] at hj
    · intro g hg
      simp [D] at hg
  have hf : circuitFun n D = graphFun G ∅ := by
    funext x
    have hz : graphFun G ∅ x = false := by
      cases hx : graphFun G ∅ x with
      | false => rfl
      | true =>
        obtain ⟨a, b, hab, _, _⟩ := (graph_true G x).mp hx
        exact (he a b hab).elim
    rw [hz]
    change (List.ofFn x).getD n false = false
    exact getD_ge _ _ (by simp)
  have hb := h.2.2 D hao hf
  change C.gates.length ≤ 0 at hb
  omega

/-- Membership in a binary gate's input list can be represented by an
    actual Fin 2 position, as required by the lift definition. -/
lemma operandPosition {n : ℕ} {C : Circuit} (h : IsAO2 n C)
    {j w : ℕ} (hj : j < C.gates.length) (hw : w ∈ (gateAt C j).inputs) :
    ∃ b : Fin 2, opnd C j b = w := by
  obtain ⟨a, b, hab⟩ := twoOperands h hj
  rw [hab] at hw
  have hpair : w = a ∨ w = b := by simpa using hw
  rcases hpair with rfl | rfl
  · exact ⟨0, by simp [opnd, hab]⟩
  · exact ⟨1, by simp [opnd, hab]⟩

/-- On a clean OR, every operand is clean. -/
theorem cleanOrOperands {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsAO2 n C) {j w : ℕ} (hj : j < C.gates.length)
    (hor : (gateAt C j).op = GateOp.or) (hc : BelowF G C j)
    (hw : w ∈ (gateAt C j).inputs) :
    ∀ x : Fin n → Bool, val C (List.ofFn x) w = true → graphFun G ∅ x = true := by
  intro x hx
  apply hc x
  exact (val_or (n := n) (by simp) hj hor).mpr ⟨w, hw, h.2.1 j hj w hw, hx⟩

/-- Every live reader of a clean gate in a least lift-fixed circuit is
    itself a clean OR. Liveness is deliberately explicit: the upstream
    lift definition does not apply to unread gates. -/
theorem cleanReader {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hlift : IsLiftFixedPoint G C)
    {r j : ℕ} (hr : r < C.gates.length) (hc : BelowF G C r)
    (hj : InOutputCone n C j) (hm : n + r ∈ (gateAt C j).inputs) :
    (gateAt C j).op = GateOp.or ∧ BelowF G C j := by
  have hclean : ∀ x : Fin n → Bool, val C (List.ofFn x) (n + r) = true →
      graphFun G ∅ x = true := hc
  have hor : (gateAt C j).op = GateOp.or := by
    rcases h.1.1 _ (gateAt_mem hj.1) with hand | hor
    · exact (noCleanAndOperand G C h j (n + r) hj.1 hm hand hclean).elim
    · exact hor
  refine ⟨hor, ?_⟩
  by_contra hn
  obtain ⟨b, hb⟩ := operandPosition h.1 hj.1 hm
  apply hlift
  refine ⟨j, hj.1, b, hj, hor, hn, ?_⟩
  rw [hb]
  refine ⟨hclean, ?_⟩
  exact ⟨fun _ => true, allTrueWires h.1 (n + r) (by omega)⟩

#print axioms allTrueWires
#print axioms rawNotClean
#print axioms distinctOperands
#print axioms outputLast
#print axioms emptyGraphNoGates
#print axioms cleanOrOperands
#print axioms cleanReader


-- Cone recurrence adapted from upstream PR #3962 (R_meta_1031_2).
-- https://github.com/open-goat/pequalnp-proofs/pull/3962/files
lemma cone_getD_lt (n : ℕ) : ∀ (gs : List Gate) (cs : List (List ℕ)) (j : ℕ), j < cs.length →
    (gs.foldl (coneStep n) cs).getD j [] = cs.getD j [] := by
  intro gs
  induction gs with
  | nil => intro cs j _; rfl
  | cons g0 gs ih =>
    intro cs j hj
    rw [List.foldl_cons]
    have hlt : j < (coneStep n cs g0).length := by
      change j < (cs ++ [_]).length
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    rw [ih (coneStep n cs g0) j hlt]
    change (cs ++ [_]).getD j [] = cs.getD j []
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
lemma cone_gate (n : ℕ) : ∀ (gs : List Gate) (cs : List (List ℕ)) (k : ℕ) (h : Gate),
    gs[k]? = some h →
    (gs.foldl (coneStep n) cs).getD (cs.length + k) [] =
      (h.inputs.filter (fun w => decide (n ≤ w ∧ w < n + (cs.length + k)))).flatMap
        (fun w => (w - n) :: (gs.foldl (coneStep n) cs).getD (w - n) []) := by
  intro gs
  induction gs with
  | nil => intro _ _ _ h; simp at h
  | cons g0 gs ih =>
    intro cs k h hk
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      subst hk
      rw [Nat.add_zero, List.foldl_cons]
      have hlt : cs.length < (coneStep n cs g0).length := by
        change cs.length < (cs ++ [_]).length
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      rw [cone_getD_lt n gs (coneStep n cs g0) cs.length hlt]
      have hself : (coneStep n cs g0).getD cs.length [] =
          (g0.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
            (fun w => (w - n) :: cs.getD (w - n) []) := by
        change (cs ++ [_]).getD cs.length [] = _
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (le_refl cs.length)]
        simp
      rw [hself]
      apply List.flatMap_congr
      intro w hw
      simp only [List.mem_filter, decide_eq_true_eq] at hw
      have hwlt : w - n < cs.length := by omega
      have hwlt2 : w - n < (coneStep n cs g0).length := by
        change w - n < (cs ++ [_]).length
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      rw [cone_getD_lt n gs (coneStep n cs g0) (w - n) hwlt2]
      change (w - n) :: cs.getD (w - n) [] = (w - n) :: (cs ++ [_]).getD (w - n) []
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hwlt]
    | succ k' =>
      simp only [List.getElem?_cons_succ] at hk
      have hlen : (coneStep n cs g0).length + k' = cs.length + (k' + 1) := by
        change (cs ++ [_]).length + k' = cs.length + (k' + 1)
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      rw [List.foldl_cons, ← hlen]
      exact ih (coneStep n cs g0) k' h hk
lemma inCone_iff_rec (n : ℕ) (C : Circuit) : ∀ (k : ℕ) (h : Gate) (i : ℕ), C.gates[k]? = some h →
    (InCone n C i k ↔ ∃ w ∈ h.inputs, n ≤ w ∧ w < n + k ∧ (i = w - n ∨ InCone n C i (w - n))) := by
  intro k h i hk
  change i ∈ (C.gates.foldl (coneStep n) []).getD k [] ↔ _
  have hcg := cone_gate n C.gates [] k h hk
  simp only [List.length_nil, Nat.zero_add] at hcg
  rw [hcg, List.mem_flatMap]
  constructor
  · rintro ⟨w, hw, hi⟩
    simp only [List.mem_filter, decide_eq_true_eq] at hw
    simp only [List.mem_cons] at hi
    exact ⟨w, hw.1, hw.2.1, hw.2.2, hi⟩
  · rintro ⟨w, hwin, hle, hlt, hi⟩
    refine ⟨w, ?_, ?_⟩
    · simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨hwin, hle, hlt⟩
    · rw [List.mem_cons]; exact hi

lemma coneRec {n : ℕ} {C : Circuit} {j : ℕ} (hj : j < C.gates.length)
    (i : ℕ) : InCone n C i j ↔
      ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ InCone n C i (w - n)) := by
  rw [gateAt_eq hj]
  exact inCone_iff_rec n C j C.gates[j] i (List.getElem?_eq_getElem hj)

lemma conePrecedes {n : ℕ} {C : Circuit} :
    ∀ j < C.gates.length, ∀ i, InCone n C i j → i < j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj i hi
    obtain ⟨w, _, hn, hw, he⟩ := (coneRec hj i).mp hi
    have hwj : w - n < j := by omega
    rcases he with he | he
    · omega
    · exact (ih _ hwj (by omega) _ he).trans hwj

lemma coneTrans {n : ℕ} {C : Circuit} :
    ∀ k < C.gates.length, ∀ i j, InCone n C i j → InCone n C j k → InCone n C i k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk i j hij hjk
    obtain ⟨w, hm, hn, hw, he⟩ := (coneRec hk j).mp hjk
    have hwk : w - n < k := by omega
    apply (coneRec hk i).mpr
    refine ⟨w, hm, hn, hw, Or.inr ?_⟩
    rcases he with rfl | he
    · exact hij
    · exact ih _ hwk (by omega) _ _ hij he

/-- A real gate of a least circuit belongs to its output cone. -/
theorem allLive {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) :
    ∀ j < C.gates.length, InOutputCone n C j := by
  have main : ∀ d : ℕ, ∀ j < C.gates.length,
      C.gates.length - j = d → InOutputCone n C j := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro j hj hd
      by_cases ho : C.output = n + j
      · exact ⟨hj, Or.inl ho⟩
      · obtain ⟨a, b, hab⟩ := twoOperands h.1 hj
        have ha := h.1.2.1 j hj a (by rw [hab]; simp)
        obtain ⟨k, hjk, hk, hm⟩ := noUnreadGate G C h j a hj ha ho
        have hkl := ih (C.gates.length - k) (by omega) k hk rfl
        have hstep : InCone n C j k := (coneRec hk j).mpr
          ⟨n + j, hm, by omega, by omega, Or.inl (by omega)⟩
        refine ⟨hj, Or.inr ?_⟩
        rcases hkl.2 with he | ⟨hn, hcone⟩
        · rw [he]
          exact ⟨by omega, by simpa using hstep⟩
        · have hout := outputLast G C h (by omega)
          have hbound : C.output - n < C.gates.length := by omega
          exact ⟨hn, coneTrans _ hbound _ _ hstep hcone⟩
  intro j hj
  exact main _ j hj rfl

/-- The clean/dirty partition at the wire level. -/
def CleanWire {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (w : ℕ) : Prop :=
  ∀ x : Fin n → Bool, val C (List.ofFn x) w = true → graphFun G ∅ x = true

lemma cleanWireGate {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (j : ℕ) : CleanWire G C (n + j) ↔ BelowF G C j := Iff.rfl

theorem cleanWireReader {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    {j w : ℕ} (hj : j < C.gates.length) (hm : w ∈ (gateAt C j).inputs)
    (hc : CleanWire G C w) : (gateAt C j).op = GateOp.or ∧ BelowF G C j := by
  have hw := h.1.2.1 j hj w hm
  by_cases hn : w < n
  · exact (rawNotClean G C ⟨w, hn⟩ hc).elim
  · obtain ⟨r, rfl⟩ : ∃ r, w = n + r := ⟨w - n, by omega⟩
    exact cleanReader G C h hl (by omega) hc (allLive G C h j hj) hm

lemma uniqueDirtyAnd {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) {r : ℕ} (hJ : junk G C = {r}) {j : ℕ}
    (hj : j < C.gates.length) (hd : ¬ BelowF G C j)
    (hand : (gateAt C j).op = GateOp.and) : j = r := by
  have hdirty : PEqualNP.CleanedNonEdge.IsDirty n G C j := by
    refine ⟨hj, ?_⟩
    by_contra hn
    apply hd
    intro x hx
    cases hf : graphFun G ∅ x with
    | true => rfl
    | false => exact (hn ⟨x, hx, hf⟩).elim
  have hm : j ∈ junk G C := by
    simp only [junk, gatesWhere, Finset.mem_filter, Finset.mem_range]
    exact ⟨hj, hand, hdirty⟩
  rw [hJ] at hm
  exact Finset.mem_singleton.mp hm

/-- Valuation of the original wires with one gate equation suspended.
    Original evaluation and concrete redirected evaluation both fit this
    interface; there are no assumptions on the suspended gate's value. -/
def EvalExcept (n : ℕ) (C : Circuit) (r : ℕ)
    (V : (Fin n → Bool) → ℕ → Bool) : Prop :=
  (∀ x (v : Fin n), V x v.val = x v) ∧
  ∀ x j, j < C.gates.length → j ≠ r →
    V x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (V x))

lemma originalEvalExcept {n : ℕ} {C : Circuit} (h : IsAO2 n C) (r : ℕ) :
    EvalExcept n C r (fun x w => val C (List.ofFn x) w) := by
  constructor
  · intro x v
    rw [val_input (n := n) (by simp) v.isLt]
    simp [List.getD_eq_getElem?_getD, v.isLt]
  · intro x j hj _
    rw [val_gate (n := n) (by simp) hj]
    congr 1
    apply List.map_congr_left
    intro i hi
    rw [ite_eq_left (h.2.1 j hj i hi)]

/-- Re-indexing a real bypass circuit gives an evaluation of precisely
    the old equations, except for the redirected gate. -/
theorem bypassEvalExcept {n : ℕ} {C : Circuit} (h : IsAO2 n C)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r) :
    EvalExcept n C r (fun x w =>
      val (bypass n C r i) (List.ofFn x) (aliasWire (n + r) i w)) := by
  constructor
  · intro x v
    rw [aliasWire_lt_self (by omega : v.val < n + r)]
    rw [bypass_val_lt (n := n) (by simp) hr v.val (by omega)]
    exact (originalEvalExcept h r).1 x v
  · intro x j hj hne
    by_cases hlt : j < r
    · rw [aliasWire_lt_self (by omega : n + j < n + r)]
      rw [bypass_val_lt (n := n) (by simp) hr (n + j) (by omega)]
      rw [(originalEvalExcept h r).2 x j hj hne]
      congr 1
      apply List.map_congr_left
      intro w hw
      have hwb := h.2.1 j hj w hw
      rw [aliasWire_lt_self (by omega : w < n + r),
        bypass_val_lt (n := n) (by simp) hr w (by omega)]
    · have hjr : r < j := by omega
      obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
      have hk : k < C.gates.length - 1 := by omega
      have hkd : k < (bypass n C r i).gates.length := by
        rw [bypass_length]; exact hk
      rw [aliasWire_gt_self (by omega : n + r < n + (k + 1))]
      have he : n + (k + 1) - 1 = n + k := by omega
      rw [he, val_gate (n := n) (by simp) hkd, gateAt_bypass hk,
        ite_eq_right (by omega : ¬ k < r)]
      simp only [aliasGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro w hw
      have hwb := h.2.1 (k + 1) hj w hw
      have hren := aliasWire_lt hi (by omega : n + r ≤ n + k)
        (by omega : w < n + k + 1)
      simp only [Function.comp_apply]
      rw [ite_eq_left hren]

/-- Support and unique-junk flag of a dirty wire, simultaneously valid
    for original evaluation and every redirected valuation. -/
def RawForm {n : ℕ} (C : Circuit) (r w : ℕ) (S : Finset (Fin n)) (b : Bool) : Prop :=
  (b = true → n + r ≤ w) ∧
  ∀ V, EvalExcept n C r V → ∀ x,
    V x w = true ↔ (∃ v ∈ S, x v = true) ∨ (b = true ∧ V x (n + r) = true)

theorem dirtyRawForm {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    {r : ℕ} (hJ : junk G C = {r}) :
    ∀ w < n + C.gates.length, ¬ CleanWire G C w →
      ∃ S b, RawForm C r w S b := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hd
    by_cases hn : w < n
    · refine ⟨{⟨w, hn⟩}, false, by simp, ?_⟩
      intro V hV x
      rw [hV.1 x ⟨w, hn⟩]
      simp
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < C.gates.length := by omega
      by_cases he : j = r
      · subst j
        refine ⟨∅, true, by simp, ?_⟩
        intro V _ x
        simp
      · have hor : (gateAt C j).op = GateOp.or := by
          rcases h.1.1 _ (gateAt_mem hj) with hand | hor
          · exact (he (uniqueDirtyAnd G C hJ hj hd hand)).elim
          · exact hor
        obtain ⟨a, b, hab⟩ := twoOperands h.1 hj
        have hma : a ∈ (gateAt C j).inputs := by rw [hab]; simp
        have hmb : b ∈ (gateAt C j).inputs := by rw [hab]; simp
        have ha := h.1.2.1 j hj a hma
        have hb := h.1.2.1 j hj b hmb
        have hda : ¬ CleanWire G C a :=
          fun hc => hd (cleanWireReader G C h hl hj hma hc).2
        have hdb : ¬ CleanWire G C b :=
          fun hc => hd (cleanWireReader G C h hl hj hmb hc).2
        obtain ⟨A, f, hf, hA⟩ := ih a ha (by omega) hda
        obtain ⟨B, g, hg, hB⟩ := ih b hb (by omega) hdb
        refine ⟨A ∪ B, f || g, ?_, ?_⟩
        · intro hb'
          rcases Bool.or_eq_true_iff.mp hb' with ht | ht
          · have := hf ht; omega
          · have := hg ht; omega
        · intro V hV x
          rw [hV.2 x j hj he, hor, hab]
          change (V x a || V x b || false) = true ↔ _
          simp only [Bool.or_false, Bool.or_eq_true_iff, hA V hV x, hB V hV x]
          simp only [Finset.mem_union]
          aesop

/-- For a unique junk gate, both its operands have pure raw support.
    Thus J is the product of two nonempty, incomparable raw OR sets. -/
theorem junkProduct {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    {r : ℕ} (hJ : junk G C = {r}) :
    ∃ a b : ℕ, ∃ A B : Finset (Fin n),
      r < C.gates.length ∧ (gateAt C r).op = GateOp.and ∧
      (gateAt C r).inputs = [a, b] ∧ a < n + r ∧ b < n + r ∧
      RawForm C r a A false ∧ RawForm C r b B false ∧
      A.Nonempty ∧ B.Nonempty ∧ ¬ A ⊆ B ∧ ¬ B ⊆ A := by
  have hm : r ∈ junk G C := by rw [hJ]; simp
  simp only [junk, gatesWhere, Finset.mem_filter, Finset.mem_range] at hm
  obtain ⟨hr, hand, _⟩ := hm
  obtain ⟨a, b, hab⟩ := twoOperands h.1 hr
  have hma : a ∈ (gateAt C r).inputs := by rw [hab]; simp
  have hmb : b ∈ (gateAt C r).inputs := by rw [hab]; simp
  have ha := h.1.2.1 r hr a hma
  have hb := h.1.2.1 r hr b hmb
  obtain ⟨A, fa, hfa, hA⟩ := dirtyRawForm G C h hl hJ a (by omega)
    (noCleanAndOperand G C h r a hr hma hand)
  obtain ⟨B, fb, hfb, hB⟩ := dirtyRawForm G C h hl hJ b (by omega)
    (noCleanAndOperand G C h r b hr hmb hand)
  have efa : fa = false := by
    cases he : fa with
    | false => rfl
    | true => have := hfa he; omega
  have efb : fb = false := by
    cases he : fb with
    | false => rfl
    | true => have := hfb he; omega
  subst fa; subst fb
  let V : (Fin n → Bool) → ℕ → Bool := fun x w => val C (List.ofFn x) w
  have hV : EvalExcept n C r V := originalEvalExcept h.1 r
  have hAs (x : Fin n → Bool) : V x a = true ↔ ∃ v ∈ A, x v = true := by
    simpa using hA V hV x
  have hBs (x : Fin n → Bool) : V x b = true ↔ ∃ v ∈ B, x v = true := by
    simpa using hB V hV x
  have hAn : A.Nonempty := by
    obtain ⟨v, hv, _⟩ := (hAs (fun _ => true)).mp
      (allTrueWires h.1 a (by omega))
    exact ⟨v, hv⟩
  have hBn : B.Nonempty := by
    obtain ⟨v, hv, _⟩ := (hBs (fun _ => true)).mp
      (allTrueWires h.1 b (by omega))
    exact ⟨v, hv⟩
  have hval (x : Fin n → Bool) : V x (n + r) = true ↔ V x a = true ∧ V x b = true := by
    change val C (List.ofFn x) (n + r) = true ↔ _
    rw [val_and (n := n) (by simp) hr hand]
    constructor
    · intro hh
      exact ⟨(hh a hma).2, (hh b hmb).2⟩
    · rintro ⟨hva, hvb⟩ w hw
      have hwb := h.1.2.1 r hr w hw
      rw [hab] at hw
      have hp : w = a ∨ w = b := by simpa using hw
      rcases hp with rfl | rfl
      · exact ⟨hwb, hva⟩
      · exact ⟨hwb, hvb⟩
  have hAB : ¬ A ⊆ B := by
    intro hs
    apply noEqualEarlier G C h r a hr ha
    intro x
    apply Bool.eq_iff_iff.mpr
    rw [hval x]
    constructor
    · exact And.left
    · intro hx
      obtain ⟨v, hv, hvx⟩ := (hAs x).mp hx
      exact ⟨hx, (hBs x).mpr ⟨v, hs hv, hvx⟩⟩
  have hBA : ¬ B ⊆ A := by
    intro hs
    apply noEqualEarlier G C h r b hr hb
    intro x
    apply Bool.eq_iff_iff.mpr
    rw [hval x]
    constructor
    · exact And.right
    · intro hx
      obtain ⟨v, hv, hvx⟩ := (hBs x).mp hx
      exact ⟨(hAs x).mpr ⟨v, hs hv, hvx⟩, hx⟩
  exact ⟨a, b, A, B, hr, hand, hab, ha, hb, ⟨hfa, hA⟩, ⟨hfb, hB⟩,
    hAn, hBn, hAB, hBA⟩

#print axioms allLive
#print axioms cleanWireReader
#print axioms bypassEvalExcept
#print axioms dirtyRawForm
#print axioms junkProduct


-- Contextual semantics: collect all clean AND tops, for ANY value
-- substituted at the unique dirty AND, not just the original valuation.

lemma junkMember {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) {r : ℕ} (hJ : junk G C = {r}) :
    r < C.gates.length ∧ (gateAt C r).op = GateOp.and ∧ ¬ BelowF G C r := by
  have hm : r ∈ junk G C := by rw [hJ]; simp
  simp only [junk, gatesWhere, Finset.mem_filter, Finset.mem_range] at hm
  obtain ⟨hr, hand, _, x, hx, hf⟩ := hm
  exact ⟨hr, hand, fun hc => by have hh := hc x hx; rw [hf] at hh; contradiction⟩

lemma evalExcept_and {n : ℕ} {C : Circuit} {r j : ℕ}
    {V : (Fin n → Bool) → ℕ → Bool} (hV : EvalExcept n C r V)
    (hj : j < C.gates.length) (hne : j ≠ r)
    (hop : (gateAt C j).op = GateOp.and) {a b : ℕ}
    (hab : (gateAt C j).inputs = [a,b]) (x : Fin n → Bool) :
    V x (n + j) = true ↔ V x a = true ∧ V x b = true := by
  rw [hV.2 x j hj hne, hop, hab]
  simp [GateOp.eval]

lemma evalExcept_or {n : ℕ} {C : Circuit} {r j : ℕ}
    {V : (Fin n → Bool) → ℕ → Bool} (hV : EvalExcept n C r V)
    (hj : j < C.gates.length) (hne : j ≠ r)
    (hop : (gateAt C j).op = GateOp.or) (x : Fin n → Bool) :
    V x (n + j) = true ↔ ∃ w ∈ (gateAt C j).inputs, V x w = true := by
  rw [hV.2 x j hj hne, hop]
  simp [GateOp.eval, List.any_map, List.any_eq_true]

lemma cleanDifferent {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) {r j : ℕ} (hJ : junk G C = {r})
    (hc : BelowF G C j) : j ≠ r := by
  intro he
  subst j
  exact (junkMember G C hJ).2.2 hc

/-- Every clean AND has two raw-support forms, at most one carrying J. -/
theorem topProduct {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    {r j : ℕ} (hJ : junk G C = {r})
    (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and)
    (hc : BelowF G C j) :
    ∃ a b : ℕ, ∃ A B : Finset (Fin n), ∃ f g : Bool,
      (gateAt C j).inputs = [a,b] ∧ RawForm C r a A f ∧
      RawForm C r b B g ∧ (f = false ∨ g = false) := by
  obtain ⟨a,b,hab⟩ := twoOperands h.1 hj
  have hma : a ∈ (gateAt C j).inputs := by rw [hab]; simp
  have hmb : b ∈ (gateAt C j).inputs := by rw [hab]; simp
  have ha := h.1.2.1 j hj a hma
  have hb := h.1.2.1 j hj b hmb
  obtain ⟨A,f,hA⟩ := dirtyRawForm G C h hl hJ a (by omega)
    (noCleanAndOperand G C h j a hj hma hand)
  obtain ⟨B,g,hB⟩ := dirtyRawForm G C h hl hJ b (by omega)
    (noCleanAndOperand G C h j b hj hmb hand)
  refine ⟨a,b,A,B,f,g,hab,hA,hB,?_⟩
  by_contra hn
  have hf : f = true := by cases f <;> simp_all
  have hg : g = true := by cases g <;> simp_all
  apply (junkMember G C hJ).2.2
  intro x hx
  let V : (Fin n → Bool) → ℕ → Bool := fun y w => val C (List.ofFn y) w
  have hV : EvalExcept n C r V := originalEvalExcept h.1 r
  have hva := (hA.2 V hV x).mpr (Or.inr ⟨hf,hx⟩)
  have hvb := (hB.2 V hV x).mpr (Or.inr ⟨hg,hx⟩)
  exact hc x ((evalExcept_and hV hj (cleanDifferent G C hJ hc) hand hab x).mpr ⟨hva,hvb⟩)

/-- A clean gate that fires must have a firing clean AND beneath it,
    even when the dirty gate is assigned a different value. -/
lemma cleanHasTop {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) {r : ℕ} (hJ : junk G C = {r})
    {V : (Fin n → Bool) → ℕ → Bool} (hV : EvalExcept n C r V) (x : Fin n → Bool) :
    ∀ j < C.gates.length, BelowF G C j → V x (n+j) = true →
      ∃ k < C.gates.length, (gateAt C k).op = GateOp.and ∧
        BelowF G C k ∧ V x (n+k) = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj hc hv
    rcases h.1.1 _ (gateAt_mem hj) with hand | hor
    · exact ⟨j,hj,hand,hc,hv⟩
    · obtain ⟨w,hm,hw⟩ := (evalExcept_or hV hj
        (cleanDifferent G C hJ hc) hor x).mp hv
      have hclean : CleanWire G C w := cleanOrOperands G C h.1 hj hor hc hm
      have hlt := h.1.2.1 j hj w hm
      by_cases hn : w < n
      · exact (rawNotClean G C ⟨w,hn⟩ hclean).elim
      · obtain ⟨k,rfl⟩ : ∃ k, w = n+k := ⟨w-n,by omega⟩
        exact ih k (by omega) (by omega) hclean hw

/-- Every true clean top propagates to the output through clean OR
    readers. This uses global liveness, not a tree assumption. -/
lemma cleanToOutput {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    {r : ℕ} (hJ : junk G C = {r})
    {V : (Fin n → Bool) → ℕ → Bool} (hV : EvalExcept n C r V) (x : Fin n → Bool) :
    ∀ j < C.gates.length, BelowF G C j → V x (n+j) = true → V x C.output = true := by
  have main : ∀ d : ℕ, ∀ j < C.gates.length, C.gates.length-j = d →
      BelowF G C j → V x (n+j) = true → V x C.output = true := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro j hj hd hc hv
      by_cases he : C.output = n+j
      · rwa [he]
      · obtain ⟨a,b,hab⟩ := twoOperands h.1 hj
        have ha := h.1.2.1 j hj a (by rw [hab]; simp)
        obtain ⟨k,hjk,hk,hm⟩ := noUnreadGate G C h j a hj ha he
        obtain ⟨hor,hck⟩ := cleanReader G C h hl hj hc (allLive G C h k hk) hm
        have hvk := (evalExcept_or hV hk (cleanDifferent G C hJ hck) hor x).mpr
          ⟨n+j,hm,hv⟩
        exact ih (C.gates.length-k) (by omega) k hk rfl hck hvk
  intro j hj hc hv
  exact main _ j hj rfl hc hv

theorem collectorSemantics {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    {r : ℕ} (hJ : junk G C = {r})
    {V : (Fin n → Bool) → ℕ → Bool} (hV : EvalExcept n C r V) (x : Fin n → Bool) :
    V x C.output = true ↔ ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧
      BelowF G C j ∧ V x (n+j) = true := by
  have hpos : 0 < C.gates.length := by have := (junkMember G C hJ).1; omega
  have ho := outputLast G C h hpos
  constructor
  · intro hv
    have hclean : BelowF G C (C.gates.length-1) := by
      intro y hy
      have he : C.eval (List.ofFn y) = graphFun G ∅ y := congrFun h.2.1 y
      rw [← he]
      change val C (List.ofFn y) C.output = true
      rw [ho]
      exact hy
    rw [ho] at hv
    exact cleanHasTop G C h hJ hV x _ (by omega) hclean hv
  · rintro ⟨j,hj,_,hc,hv⟩
    exact cleanToOutput G C h hl hJ hV x j hj hc hv

lemma rawFormLost {n : ℕ} {C : Circuit} {r w : ℕ} {S : Finset (Fin n)} {b : Bool}
    (hS : RawForm C r w S b)
    {V W : (Fin n → Bool) → ℕ → Bool}
    (hV : EvalExcept n C r V) (hW : EvalExcept n C r W)
    (x : Fin n → Bool) (hv : V x w = true) (hw : W x w = false) :
    b = true ∧ V x (n+r) = true ∧ W x (n+r) = false := by
  have hn : ¬ W x w = true := by rw [hw]; decide
  rcases (hS.2 V hV x).mp hv with hs | ⟨hb,hj⟩
  · exact (hn ((hS.2 W hW x).mpr (Or.inl hs))).elim
  · refine ⟨hb,hj,?_⟩
    cases he : W x (n+r) with
    | false => rfl
    | true => exact (hn ((hS.2 W hW x).mpr (Or.inr ⟨hb,he⟩))).elim

/-- A full strict-deletion subcase: a unique junk with overlap exactly
    one vertex, and no exposed centre on the opposite side of a top.
    The replacement is the real raw overlap wire, not a new gate.

    The no-exposure hypothesis is stated directly in terms of the
    canonical semantic forms supplied by topProduct. -/
theorem noSingleOverlapNoExposure {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (h : IsLeastAO G C)
    (hl : IsLiftFixedPoint G C) {r a b : ℕ} (hJ : junk G C = {r})
    (hab : (gateAt C r).inputs = [a,b])
    (A B : Finset (Fin n)) (hA : RawForm C r a A false)
    (hB : RawForm C r b B false) (c : Fin n)
    (hcA : c ∈ A) (hcB : c ∈ B)
    (hI : ∀ v ∈ A, v ∈ B → v = c)
    (hno : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      BelowF G C j → ∀ p q S T f g,
      (gateAt C j).inputs = [p,q] →
      RawForm C r p S f → RawForm C r q T g →
      (f = true → ∀ v ∈ T, v ∉ A ∧ v ∉ B) ∧
      (g = true → ∀ v ∈ S, v ∉ A ∧ v ∉ B)) : False := by
  obtain ⟨hr,hand,_⟩ := junkMember G C hJ
  have hi : c.val < n+r := by omega
  let V : (Fin n → Bool) → ℕ → Bool := fun x w => val C (List.ofFn x) w
  let D := bypass n C r c.val
  let W : (Fin n → Bool) → ℕ → Bool := fun x w =>
    val D (List.ofFn x) (aliasWire (n+r) c.val w)
  have hV : EvalExcept n C r V := originalEvalExcept h.1 r
  have hW : EvalExcept n C r W := bypassEvalExcept h.1 hr hi
  have hD : IsAO2 n D := by
    rw [← erase_eq_bypass n C r c.val hr]
    exact erase_exactAO h.1 hr hi
  have hnew (x : Fin n → Bool) : W x (n+r) = x c := by
    dsimp [W,D]
    rw [aliasWire_self, bypass_val_lt (n := n) (by simp) hr c.val hi]
    exact hV.1 x c
  have hprod (x : Fin n → Bool) : V x (n+r) = true ↔
      (∃ v ∈ A, x v = true) ∧ (∃ v ∈ B, x v = true) := by
    have hAs : V x a = true ↔ ∃ v ∈ A, x v = true := by simpa using hA.2 V hV x
    have hBs : V x b = true ↔ ∃ v ∈ B, x v = true := by simpa using hB.2 V hV x
    change val C (List.ofFn x) (n+r) = true ↔ _
    rw [val_and (n := n) (by simp) hr hand]
    have hma : a ∈ (gateAt C r).inputs := by rw [hab]; simp
    have hmb : b ∈ (gateAt C r).inputs := by rw [hab]; simp
    constructor
    · intro hh
      exact ⟨hAs.mp (hh a hma).2, hBs.mp (hh b hmb).2⟩
    · rintro ⟨hva,hvb⟩ w hw
      have hlt := h.1.2.1 r hr w hw
      rw [hab] at hw
      have he : w = a ∨ w = b := by simpa using hw
      rcases he with rfl | rfl
      · exact ⟨hlt,hAs.mpr hva⟩
      · exact ⟨hlt,hBs.mpr hvb⟩
  have hneg (x : Fin n → Bool) : D.eval (List.ofFn x) = true →
      C.eval (List.ofFn x) = true := by
    apply bypass_eval_rel (R := fun a b => b = true → a = true)
      (fun _ => id) opMono_reverse (n := n) (by simp)
      (mono_ops (ao_mono h.1)) hr (Or.inl hi)
    intro hx
    have hcx : x c = true := (hV.1 x c).symm.trans hx
    exact (hprod x).mpr ⟨⟨c,hcA,hcx⟩,⟨c,hcB,hcx⟩⟩
  -- Every accepted edge survives the real earlier-wire substitution.
  have hedge (u v : Fin n) (huv : G.Adj u v) :
      D.eval (List.ofFn (pairInput u v)) = true := by
    let x := pairInput u v
    have hF : graphFun G ∅ x = true := pair_true G u v huv
    have hvo : V x C.output = true := (congrFun h.2.1 x).trans hF
    obtain ⟨j,hj,hop,hclean,hjv⟩ := (collectorSemantics G C h hl hJ hV x).mp hvo
    obtain ⟨p,q,S,T,f,g,hpq,hS,hT,hfg⟩ := topProduct G C h hl hJ hj hop hclean
    have hdiff := cleanDifferent G C hJ hclean
    obtain ⟨hvp,hvq⟩ := (evalExcept_and hV hj hdiff hop hpq x).mp hjv
    have hsafe := hno j hj hop hclean p q S T f g hpq hS hT
    have pairImpossible (z : Fin n) (hz : x z = true) (hzA : z ∉ A) (hzB : z ∉ B)
        (hJv : V x (n+r) = true) (hJw : W x (n+r) = false) : False := by
      obtain ⟨⟨a',ha',hax⟩,⟨b',hb',hbx⟩⟩ := (hprod x).mp hJv
      have hcx : x c = false := (hnew x).symm.trans hJw
      have hne : a' ≠ b' := by
        intro he
        have hac := hI a' ha' (he ▸ hb')
        have ht : x c = true := hac ▸ hax
        rw [hcx] at ht
        contradiction
      have h1 : a' = u ∨ a' = v := by simpa [x,pairInput] using hax
      have h2 : b' = u ∨ b' = v := by simpa [x,pairInput] using hbx
      have h3 : z = u ∨ z = v := by simpa [x,pairInput] using hz
      have hza : z ≠ a' := fun he => hzA (he.symm ▸ ha')
      have hzb : z ≠ b' := fun he => hzB (he.symm ▸ hb')
      aesop
    have hwp : W x p = true := by
      cases he : W x p with
      | true => rfl
      | false =>
        obtain ⟨hf,hjv',hjw⟩ := rawFormLost hS hV hW x hvp he
        have hg : g = false := by rcases hfg with hh | hh
                                 · rw [hf] at hh; contradiction
                                 · exact hh
        obtain ⟨z,hz,hzx⟩ := (hT.2 V hV x).mp hvq |>.resolve_right
          (by simp [hg])
        obtain ⟨hzA,hzB⟩ := hsafe.1 hf z hz
        exact (pairImpossible z hzx hzA hzB hjv' hjw).elim
    have hwq : W x q = true := by
      cases he : W x q with
      | true => rfl
      | false =>
        obtain ⟨hg,hjv',hjw⟩ := rawFormLost hT hV hW x hvq he
        have hf : f = false := by rcases hfg with hh | hh
                                 · exact hh
                                 · rw [hg] at hh; contradiction
        obtain ⟨z,hz,hzx⟩ := (hS.2 V hV x).mp hvp |>.resolve_right
          (by simp [hf])
        obtain ⟨hzA,hzB⟩ := hsafe.2 hg z hz
        exact (pairImpossible z hzx hzA hzB hjv' hjw).elim
    have htop := (evalExcept_and hW hj hdiff hop hpq x).mpr ⟨hwp,hwq⟩
    exact (collectorSemantics G C h hl hJ hW x).mpr ⟨j,hj,hop,hclean,htop⟩
  have heq : circuitFun n D = graphFun G ∅ := by
    funext x
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hx
      exact (congrFun h.2.1 x) ▸ hneg x hx
    · intro hx
      obtain ⟨u,v,huv,hu,hv⟩ := (graph_true G x).mp hx
      apply circuit_monotone n D (ao_mono hD) (pairInput u v) x ?_ (hedge u v huv)
      intro w hw
      have he : w = u ∨ w = v := by simpa [pairInput] using hw
      rcases he with rfl | rfl
      · exact hu
      · exact hv
  have hmin := h.2.2 D hD heq
  have hsize : D.size = C.gates.length-1 := bypass_length n C r c.val
  change C.gates.length ≤ D.size at hmin
  omega

#print axioms topProduct
#print axioms collectorSemantics
#print axioms noSingleOverlapNoExposure

end ResearchVerification.OneJunkErase
