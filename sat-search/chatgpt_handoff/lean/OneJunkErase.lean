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

noncomputable def cleanGates {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (op : GateOp) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter fun j => (gateAt C j).op = op ∧ BelowF G C j

lemma mem_cleanGates {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (op : GateOp) (j : ℕ) :
    j ∈ cleanGates G C op ↔ j < C.gates.length ∧ (gateAt C j).op = op ∧ BelowF G C j := by
  classical
  simp [cleanGates]

/-- Incidence counting in the original gate list gives the collector lower
    bound, even if a clean gate has multiple clean readers. -/
theorem collectorOrLower {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C) :
    (cleanGates G C GateOp.and).card ≤ (cleanGates G C GateOp.or).card + 1 := by
  classical
  let A := cleanGates G C GateOp.and
  let O := cleanGates G C GateOp.or
  let operands := fun j => (gateAt C j).inputs.toFinset
  have hd : Disjoint A O := by
    refine Finset.disjoint_left.mpr ?_
    intro j hj hk
    have ha := ((mem_cleanGates G C GateOp.and j).mp hj).2.1
    have ho := ((mem_cleanGates G C GateOp.or j).mp hk).2.1
    rw [ha] at ho
    contradiction
  have hc : ∀ j ∈ A ∪ O, j < C.gates.length ∧ BelowF G C j := by
    intro j hj
    rcases Finset.mem_union.mp hj with hj | hj
    · obtain ⟨hj, _, hc⟩ := (mem_cleanGates G C GateOp.and j).mp hj
      exact ⟨hj, hc⟩
    · obtain ⟨hj, _, hc⟩ := (mem_cleanGates G C GateOp.or j).mp hj
      exact ⟨hj, hc⟩
  have hcover : (A ∪ O).image (n + ·) ⊆ insert C.output (O.biUnion operands) := by
    intro w hw
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hj, hjc⟩ := hc j hj
    by_cases he : C.output = n + j
    · exact Finset.mem_insert.mpr (Or.inl he.symm)
    · obtain ⟨a, b, hab⟩ := twoOperands h.1 hj
      have ha := h.1.2.1 j hj a (by rw [hab]; simp)
      obtain ⟨k, _, hk, hm⟩ := noUnreadGate G C h j a hj ha he
      obtain ⟨hor, hkc⟩ := cleanReader G C h hl hj hjc (allLive G C h k hk) hm
      apply Finset.mem_insert.mpr
      exact Or.inr (Finset.mem_biUnion.mpr
        ⟨k, (mem_cleanGates G C GateOp.or k).mpr ⟨hk, hor, hkc⟩, List.mem_toFinset.mpr hm⟩)
  have hslots : (O.biUnion operands).card ≤ O.card * 2 := by
    apply Finset.card_biUnion_le_card_mul
    intro j hj
    have hj' := ((mem_cleanGates G C GateOp.or j).mp hj).1
    obtain ⟨a, b, hab⟩ := twoOperands h.1 hj'
    calc
      (operands j).card ≤ (gateAt C j).inputs.length := List.toFinset_card_le _
      _ = 2 := by simp [hab]
  have hcard := Finset.card_le_card hcover
  rw [Finset.card_image_of_injective _ (fun _ _ he => Nat.add_left_cancel he),
    Finset.card_union_of_disjoint hd] at hcard
  have hins := Finset.card_insert_le C.output (O.biUnion operands)
  change A.card ≤ O.card + 1
  omega

#print axioms collectorOrLower

private def appendBinary (D : Circuit) (op : GateOp) (a b : ℕ) : Circuit :=
  ⟨D.gates ++ [⟨op, [a, b]⟩], D.output⟩

private lemma appendBinary_spec {n : ℕ} {D : Circuit} (h : IsAO2 n D)
    {op : GateOp} (hop : op = GateOp.and ∨ op = GateOp.or)
    {a b : ℕ} (ha : a < n + D.gates.length) (hb : b < n + D.gates.length) :
    let E := appendBinary D op a b
    E.gates.length = D.gates.length + 1 ∧ IsAO2 n E ∧
      (∀ (x : Fin n → Bool) w, w < n + D.gates.length →
        val E (List.ofFn x) w = val D (List.ofFn x) w) ∧
      (∀ x : Fin n → Bool, val E (List.ofFn x) (n + D.gates.length) =
        op.eval [val D (List.ofFn x) a, val D (List.ofFn x) b]) := by
  let E := appendBinary D op a b
  have hlen : E.gates.length = D.gates.length + 1 := by simp [E, appendBinary]
  have old : ∀ j < D.gates.length, gateAt E j = gateAt D j := by
    intro j hj
    rw [gateAt_eq (by omega : j < E.gates.length), gateAt_eq hj]
    exact List.getElem_append_left hj
  have fresh : gateAt E D.gates.length = ⟨op, [a, b]⟩ := by
    rw [gateAt_eq (by omega : D.gates.length < E.gates.length)]
    simp [E, appendBinary, List.getElem_append_right (le_refl D.gates.length)]
  have keep (x : Fin n → Bool) (w : ℕ) (hw : w < n + D.gates.length) :
      val E (List.ofFn x) w = val D (List.ofFn x) w := by
    exact val_prefix (n := n) (by simp) le_rfl (by omega) old w hw
  refine ⟨hlen, ⟨?_, ?_, ?_⟩, keep, ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact h.1 _ hg
    · obtain rfl := List.mem_singleton.mp hg
      exact hop
  · intro j hj w hw
    change j < E.gates.length at hj
    by_cases hj' : j < D.gates.length
    · rw [old j hj'] at hw
      exact h.2.1 j hj' w hw
    · have he : j = D.gates.length := by omega
      subst j
      rw [fresh] at hw
      have hw' : w = a ∨ w = b := by simpa using hw
      rcases hw' with rfl | rfl
      · exact ha
      · exact hb
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact h.2.2 _ hg
    · obtain rfl := List.mem_singleton.mp hg
      rfl
  · intro x
    rw [val_gate (n := n) (by simp) (by omega : D.gates.length < E.gates.length), fresh]
    simp [ha, hb, keep x a ha, keep x b hb]

private def RetainedWire (n : ℕ) (P : ℕ → Prop) (k w : ℕ) : Prop :=
  w < n ∨ ∃ j < k, P j ∧ w = n + j

/-- Compile an ancestor-closed selection, preserving its raw and gate values. -/
private lemma compileSelection {n : ℕ} (C : Circuit) (h : IsAO2 n C)
    (P : ℕ → Prop) [DecidablePred P]
    (closed : ∀ j < C.gates.length, P j → ∀ w ∈ (gateAt C j).inputs,
      RetainedWire n P j w) :
    ∀ k ≤ C.gates.length, ∃ (D : Circuit) (ρ : ℕ → ℕ), IsAO2 n D ∧
      D.gates.length = ((Finset.range k).filter P).card ∧
      ∀ w, RetainedWire n P k w → ρ w < n + D.gates.length ∧
        ∀ x : Fin n → Bool, val D (List.ofFn x) (ρ w) = val C (List.ofFn x) w := by
  intro k
  induction k with
  | zero =>
    intro _
    let D : Circuit := ⟨[], 0⟩
    refine ⟨D, id, ⟨?_, ?_, ?_⟩, by simp [D], ?_⟩
    · simp [AndOrOnly, D]
    · simp [ReadsBack, D]
    · simp [D]
    · intro w hw
      have hw' : w < n := by simpa [RetainedWire] using hw
      refine ⟨by simpa [D] using hw', ?_⟩
      intro x
      change val D (List.ofFn x) w = val C (List.ofFn x) w
      rw [val_input (n := n) (by simp) hw', val_input (n := n) (by simp) hw']
  | succ k ih =>
    intro hk
    obtain ⟨D, ρ, hD, hlen, hρ⟩ := ih (by omega)
    have hj : k < C.gates.length := by omega
    have liftOld {w : ℕ} (hw : RetainedWire n P (k + 1) w) (hne : w ≠ n + k) :
        RetainedWire n P k w := by
      rcases hw with hw | ⟨j, hj, hp, rfl⟩
      · exact Or.inl hw
      · exact Or.inr ⟨j, by omega, hp, rfl⟩
    by_cases hp : P k
    · obtain ⟨a, b, hab⟩ := twoOperands h hj
      have hma : a ∈ (gateAt C k).inputs := by rw [hab]; simp
      have hmb : b ∈ (gateAt C k).inputs := by rw [hab]; simp
      have ha := hρ a (closed k hj hp a hma)
      have hb := hρ b (closed k hj hp b hmb)
      let op := (gateAt C k).op
      let E := appendBinary D op (ρ a) (ρ b)
      obtain ⟨hlenE, hE, hold, hnew⟩ := appendBinary_spec hD (h.1 _ (gateAt_mem hj)) ha.1 hb.1
      change E.gates.length = D.gates.length + 1 at hlenE
      refine ⟨E, fun w => if w = n + k then n + D.gates.length else ρ w, hE, ?_, ?_⟩
      · rw [hlenE, hlen, Finset.range_add_one, Finset.filter_insert, ite_eq_left hp,
          Finset.card_insert_of_notMem (by simp)]
      · intro w hw
        by_cases he : w = n + k
        · subst w
          dsimp only
          rw [ite_eq_left rfl]
          refine ⟨by omega, ?_⟩
          intro x
          rw [hnew x, ha.2 x, hb.2 x, val_gate (n := n) (by simp) hj, hab]
          have hlt := h.2.1 k hj a hma
          have hlt' := h.2.1 k hj b hmb
          simp [hlt, hlt']
        · dsimp only
          rw [ite_eq_right he]
          have ht := hρ w (liftOld hw he)
          exact ⟨by omega, fun x => (hold x _ ht.1).trans (ht.2 x)⟩
    · refine ⟨D, ρ, hD, ?_, ?_⟩
      · rw [hlen, Finset.range_add_one, Finset.filter_insert, ite_eq_right hp]
      · intro w hw
        apply hρ w (liftOld hw ?_)
        rintro rfl
        rcases hw with hw | ⟨j, _, hp', he⟩
        · omega
        · have he' : j = k := by omega
          exact hp (he' ▸ hp')

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
    dsimp only
    rw [val_input (n := n) (by simp) v.isLt]
    simp [List.getD_eq_getElem?_getD, v.isLt]
  · intro x j hj _
    dsimp only
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
    dsimp only
    rw [aliasWire_lt_self (by omega : v.val < n + r)]
    rw [bypass_val_lt (n := n) (by simp) hr v.val (by omega)]
    exact (originalEvalExcept h r).1 x v
  · intro x j hj hne
    dsimp only
    by_cases hlt : j < r
    · rw [aliasWire_lt_self (by omega : n + j < n + r)]
      rw [bypass_val_lt (n := n) (by simp) hr (n + j) (by omega)]
      have heq := (originalEvalExcept h r).2 x j hj hne
      dsimp only at heq
      rw [heq]
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
      ∃ (S : Finset (Fin n)) (b : Bool), RawForm C r w S b := by
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
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
            List.any_nil, id_eq, Bool.or_false, Bool.or_eq_true_iff, hA V hV x, hB V hV x,
            Finset.mem_union]
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
    (C : Circuit) (h : IsLeastAO G C) {r : ℕ}
    (hskip : ∀ j < C.gates.length, BelowF G C j → j ≠ r)
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
        (hskip j hj hc) hor x).mp hv
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
    {r : ℕ} (hskip : ∀ j < C.gates.length, BelowF G C j → j ≠ r)
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
        have hvk := (evalExcept_or hV hk (hskip k hk hck) hor x).mpr
          ⟨n+j,hm,hv⟩
        exact ih (C.gates.length-k) (by omega) k hk rfl hck hvk
  intro j hj hc hv
  exact main _ j hj rfl hc hv

private theorem collectorSemanticsExcept {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    (hpos : 0 < C.gates.length) {r : ℕ} (hskip : ∀ j < C.gates.length, BelowF G C j → j ≠ r)
    {V : (Fin n → Bool) → ℕ → Bool} (hV : EvalExcept n C r V) (x : Fin n → Bool) :
    V x C.output = true ↔ ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧
      BelowF G C j ∧ V x (n+j) = true := by
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
    exact cleanHasTop G C h hskip hV x _ (by omega) hclean hv
  · rintro ⟨j,hj,_,hc,hv⟩
    exact cleanToOutput G C h hl hskip hV x j hj hc hv

theorem collectorSemantics {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    {r : ℕ} (hJ : junk G C = {r})
    {V : (Fin n → Bool) → ℕ → Bool} (hV : EvalExcept n C r V) (x : Fin n → Bool) :
    V x C.output = true ↔ ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧
      BelowF G C j ∧ V x (n+j) = true := by
  have hr := (junkMember G C hJ).1
  exact collectorSemanticsExcept G C h hl (by omega) (fun _ _ hc => cleanDifferent G C hJ hc) hV x

private lemma compileCollector {n : ℕ} (D : Circuit) (hD : IsAO2 n D)
    (a : ℕ) (ha : a < n + D.gates.length) (rest : List ℕ)
    (hr : ∀ b ∈ rest, b < n + D.gates.length) :
    ∃ E : Circuit, IsAO2 n E ∧ E.gates.length = D.gates.length + rest.length ∧
      (∀ (x : Fin n → Bool) b, b < n + D.gates.length →
        val E (List.ofFn x) b = val D (List.ofFn x) b) ∧
      (∀ x : Fin n → Bool, E.eval (List.ofFn x) = true ↔
        val D (List.ofFn x) a = true ∨ ∃ b ∈ rest, val D (List.ofFn x) b = true) ∧
      E.output < n + E.gates.length := by
  induction rest with
  | nil =>
    exact ⟨⟨D.gates, a⟩, hD, by simp, fun _ _ _ => rfl,
      fun x => by simp [Circuit.eval, val, Circuit.wires], ha⟩
  | cons b rest ih =>
    obtain ⟨F, hF, hlen, hkeep, heval, hout⟩ := ih
      (fun c hc => hr c (List.mem_cons_of_mem _ hc))
    have hb := hr b (by simp)
    have hbF : b < n + F.gates.length := by omega
    let F' := appendBinary F GateOp.or F.output b
    obtain ⟨hlen', hF', hkeep', hnew⟩ := appendBinary_spec hF (Or.inr rfl) hout hbF
    let E : Circuit := ⟨F'.gates, n + F.gates.length⟩
    have hsize : E.gates.length = F.gates.length + 1 := hlen'
    refine ⟨E, hF', by simp only [List.length_cons]; omega, ?_, ?_, ?_⟩
    · intro x c hc
      exact (hkeep' x c (by omega)).trans (hkeep x c hc)
    · intro x
      change val F' (List.ofFn x) (n + F.gates.length) = true ↔ _
      rw [hnew x, hkeep x b hb]
      simp only [GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true,
        ← eval_eq_val, List.mem_cons]
      aesop
    · change n + F.gates.length < n + E.gates.length
      omega

/-- Exact collector budget in the original list. Recompile the gates outside
    the collector and append a chain with one OR per additional clean AND. -/
theorem collectorOrExact {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C) :
    (cleanGates G C GateOp.or).card = (cleanGates G C GateOp.and).card - 1 := by
  classical
  by_cases hzero : C.gates.length = 0
  · simp [cleanGates, hzero]
  have hpos : 0 < C.gates.length := by omega
  let A := cleanGates G C GateOp.and
  let O := cleanGates G C GateOp.or
  let P := fun j => ¬ ((gateAt C j).op = GateOp.or ∧ BelowF G C j)
  have hspec (x : Fin n → Bool) : C.eval (List.ofFn x) = true ↔
      ∃ j ∈ A, val C (List.ofFn x) (n + j) = true := by
    have he := collectorSemanticsExcept G C h hl hpos (r := C.gates.length)
      (fun _ hj _ hne => (Nat.ne_of_lt hj) hne) (originalEvalExcept h.1 C.gates.length) x
    simpa only [eval_eq_val, A, mem_cleanGates, and_assoc] using he
  have hA : A.Nonempty := by
    have hout := outputLast G C h hpos
    have hv : C.eval (List.ofFn (fun _ : Fin n => true)) = true := by
      rw [eval_eq_val]
      exact allTrueWires h.1 _ (by omega)
    obtain ⟨j, hj, _⟩ := (hspec _).mp hv
    exact ⟨j, hj⟩
  have closed (j : ℕ) (hj : j < C.gates.length) (hp : P j)
      (w : ℕ) (hm : w ∈ (gateAt C j).inputs) : RetainedWire n P j w := by
    have hlt := h.1.2.1 j hj w hm
    by_cases hw : w < n
    · exact Or.inl hw
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      refine Or.inr ⟨k, by omega, ?_, rfl⟩
      exact fun hc => hp (cleanWireReader G C h hl hj hm hc.2)
  obtain ⟨D, ρ, hD, hlen, hρ⟩ := compileSelection C h.1 P closed C.gates.length le_rfl
  have hbase : D.gates.length + O.card = C.gates.length := by
    rw [hlen, Nat.add_comm]
    exact (Finset.card_filter_add_card_filter_not
      (s := Finset.range C.gates.length) (p := fun j => (gateAt C j).op = GateOp.or ∧ BelowF G C j)).trans
      (Finset.card_range _)
  have htop (j : ℕ) (hj : j ∈ A) : ρ (n + j) < n + D.gates.length ∧
      ∀ x : Fin n → Bool, val D (List.ofFn x) (ρ (n + j)) = val C (List.ofFn x) (n + j) := by
    obtain ⟨hj, ha, _⟩ := (mem_cleanGates G C GateOp.and j).mp hj
    apply hρ (n + j)
    refine Or.inr ⟨j, hj, ?_, rfl⟩
    intro hh
    rw [ha] at hh
    exact GateOp.noConfusion hh.1
  obtain ⟨i, hi⟩ := hA
  let rest := (A.erase i).toList.map fun j => ρ (n + j)
  have hr : ∀ w ∈ rest, w < n + D.gates.length := by
    intro w hw
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hw
    exact (htop j (Finset.mem_of_mem_erase (Finset.mem_toList.mp hj))).1
  obtain ⟨E, hE, hsize, _, hrun, _⟩ := compileCollector D hD _ (htop i hi).1 rest hr
  have hcorrect : circuitFun n E = graphFun G ∅ := by
    rw [← h.2.1]
    funext x
    apply Bool.eq_iff_iff.mpr
    change E.eval (List.ofFn x) = true ↔ C.eval (List.ofFn x) = true
    rw [hrun x, hspec x, (htop i hi).2 x]
    constructor
    · rintro (hv | ⟨w, hw, hv⟩)
      · exact ⟨i, hi, hv⟩
      · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hw
        have hjA := Finset.mem_of_mem_erase (Finset.mem_toList.mp hj)
        exact ⟨j, hjA, (htop j hjA).2 x ▸ hv⟩
    · rintro ⟨j, hj, hv⟩
      by_cases he : j = i
      · exact Or.inl (he ▸ hv)
      · refine Or.inr ⟨ρ (n + j), List.mem_map.mpr ⟨j, ?_, rfl⟩, ?_⟩
        · exact Finset.mem_toList.mpr (Finset.mem_erase.mpr ⟨he, hj⟩)
        · exact ((htop j hj).2 x).trans hv
  have hmin := h.2.2 E hE hcorrect
  change C.gates.length ≤ E.gates.length at hmin
  have hrest : rest.length + 1 = A.card := by
    simpa [rest] using Finset.card_erase_add_one hi
  have hlo := collectorOrLower G C h hl
  change A.card ≤ O.card + 1 at hlo
  change O.card = A.card - 1
  omega

#print axioms collectorOrExact

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
    change IsAO2 n (bypass n C r c.val)
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
        have hg : g = false := by
          rcases hfg with hh | hh
          · rw [hf] at hh; contradiction
          · exact hh
        have hraw : ∃ z ∈ T, x z = true := by
          simpa [hg] using (hT.2 V hV x).mp hvq
        obtain ⟨z,hz,hzx⟩ := hraw
        obtain ⟨hzA,hzB⟩ := hsafe.1 hf z hz
        exact (pairImpossible z hzx hzA hzB hjv' hjw).elim
    have hwq : W x q = true := by
      cases he : W x q with
      | true => rfl
      | false =>
        obtain ⟨hg,hjv',hjw⟩ := rawFormLost hT hV hW x hvq he
        have hf : f = false := by
          rcases hfg with hh | hh
          · exact hh
          · rw [hg] at hh; contradiction
        have hraw : ∃ z ∈ S, x z = true := by
          simpa [hf] using (hS.2 V hV x).mp hvp
        obtain ⟨z,hz,hzx⟩ := hraw
        obtain ⟨hzA,hzB⟩ := hsafe.2 hg z hz
        exact (pairImpossible z hzx hzA hzB hjv' hjw).elim
    have htop := (evalExcept_and hW hj hdiff hop hpq x).mpr ⟨hwp,hwq⟩
    exact (collectorSemantics G C h hl hJ hW x).mpr ⟨j,hj,hop,hclean,htop⟩
  have heq : circuitFun n D = graphFun G ∅ := by
    funext x
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hx
      have he : C.eval (List.ofFn x) = graphFun G ∅ x := congrFun h.2.1 x
      rw [← he]
      exact hneg x hx
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

private def hits {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) : Prop :=
  ∃ v ∈ S, x v = true

private lemma adjOfPair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {a b : Fin n} (h : graphFun G ∅ (pairInput a b) = true) : G.Adj a b := by
  obtain ⟨u, v, huv, hu, hv⟩ := (graph_true G _).mp h
  have hu' : u = a ∨ u = b := by simpa [pairInput] using hu
  have hv' : v = a ∨ v = b := by simpa [pairInput] using hv
  rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl
  · exact (G.ne_of_adj huv rfl).elim
  · exact huv
  · exact (G.adj_comm _ _).mp huv
  · exact (G.ne_of_adj huv rfl).elim

private lemma originalJunkProduct {n : ℕ} {C : Circuit} (h : IsAO2 n C)
    {r a b : ℕ} (hr : r < C.gates.length) (hand : (gateAt C r).op = GateOp.and)
    (hab : (gateAt C r).inputs = [a, b]) {A B : Finset (Fin n)}
    (hA : RawForm C r a A false) (hB : RawForm C r b B false) (x : Fin n → Bool) :
    val C (List.ofFn x) (n + r) = true ↔ hits A x ∧ hits B x := by
  let V := fun (y : Fin n → Bool) w => val C (List.ofFn y) w
  have hV : EvalExcept n C r V := originalEvalExcept h r
  have he := evalExcept_and (originalEvalExcept h C.gates.length) hr (Nat.ne_of_lt hr) hand hab x
  have ha : V x a = true ↔ hits A x := by simpa [hits] using hA.2 V hV x
  have hb : V x b = true ↔ hits B x := by simpa [hits] using hB.2 V hV x
  change V x (n + r) = true ↔ _
  change V x (n + r) = true ↔ V x a = true ∧ V x b = true at he
  rw [he, ha, hb]

/-- A clean top has an oriented form, with the optional junk carried
    exclusively on the first side. -/
private def OrientedTop {n : ℕ} (C : Circuit) (r j : ℕ)
    (S T : Finset (Fin n)) (f : Bool) : Prop :=
  ∀ V, EvalExcept n C r V → ∀ x,
    V x (n + j) = true ↔ (hits S x ∨ (f = true ∧ V x (n + r) = true)) ∧ hits T x

private lemma orientedTop {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    {r j : ℕ} (hJ : junk G C = {r}) (hj : j < C.gates.length)
    (hand : (gateAt C j).op = GateOp.and) (hc : BelowF G C j) :
    ∃ (S T : Finset (Fin n)) (f : Bool), OrientedTop C r j S T f := by
  obtain ⟨a, b, A, B, f, g, hab, hA, hB, he⟩ := topProduct G C h hl hJ hj hand hc
  have hne := cleanDifferent G C hJ hc
  rcases he with hf | hg
  · refine ⟨B, A, g, fun V hV x => ?_⟩
    rw [evalExcept_and hV hj hne hand hab x, hA.2 V hV x, hB.2 V hV x]
    simp [hf, hits, and_comm]
  · refine ⟨A, B, f, fun V hV x => ?_⟩
    rw [evalExcept_and hV hj hne hand hab x, hA.2 V hV x, hB.2 V hV x]
    simp [hg, hits]

private lemma carrierCross {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {C : Circuit} (h : IsAO2 n C) {r j : ℕ} {A B S T : Finset (Fin n)}
    (hprod : ∀ x : Fin n → Bool, val C (List.ofFn x) (n + r) = true ↔ hits A x ∧ hits B x)
    (hc : BelowF G C j) (ht : OrientedTop C r j S T true)
    {a b u v : Fin n} (ha : a ∈ A) (hb : b ∈ B) (hv : v ∈ T)
    (ha' : a = u ∨ a = v) (hb' : b = u ∨ b = v) : G.Adj u v := by
  let x := pairInput u v
  have ha'' : x a = true := by simpa [x, pairInput] using ha'
  have hb'' : x b = true := by simpa [x, pairInput] using hb'
  have hv' : x v = true := by simp [x, pairInput]
  have hj := (hprod x).mpr ⟨⟨a, ha, ha''⟩, ⟨b, hb, hb''⟩⟩
  exact adjOfPair G (hc x ((ht _ (originalEvalExcept h r) x).mpr
    ⟨Or.inr ⟨rfl, hj⟩, ⟨v, hv, hv'⟩⟩))

private lemma commonNeighborUnique {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) {u v c d : Fin n} (hne : u ≠ v)
    (huc : G.Adj u c) (hvc : G.Adj v c) (hud : G.Adj u d) (hvd : G.Adj v d) : d = c := by
  let N := Finset.univ.filter fun w => G.Adj u w ∧ G.Adj v w
  have hN : N.card ≤ 1 := h4 u v hne
  have hc : c ∈ N := by simp [N, huc, hvc]
  have hd : d ∈ N := by simp [N, hud, hvd]
  exact Finset.card_le_one.mp hN d hd c hc

private lemma overlapCarrierCentre {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {C : Circuit} (h : IsAO2 n C) (h4 : NoFourCycle G) {r j : ℕ}
    {A B S T : Finset (Fin n)}
    (hprod : ∀ x : Fin n → Bool, val C (List.ofFn x) (n + r) = true ↔ hits A x ∧ hits B x)
    (hc : BelowF G C j) (ht : OrientedTop C r j S T true)
    {u v c : Fin n} (huA : u ∈ A) (huB : u ∈ B) (hvA : v ∈ A) (hvB : v ∈ B)
    (hne : u ≠ v) (huc : G.Adj u c) (hvc : G.Adj v c) :
    ∀ x : Fin n → Bool, hits T x → x c = true := by
  rintro x ⟨d, hd, hx⟩
  have hud := carrierCross G h hprod hc ht huA huB hd (Or.inl rfl) (Or.inl rfl)
  have hvd := carrierCross G h hprod hc ht hvA hvB hd (Or.inl rfl) (Or.inl rfl)
  exact commonNeighborUnique G h4 hne huc hvc hud hvd ▸ hx

/-- The opposite operand of a junk-carrying top is the raw centre wire
    itself. A gate computing that singleton would be redundant. -/
theorem twoOverlapOppositeRaw {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (h4 : NoFourCycle G)
    {r a b j p q : ℕ} (hJ : junk G C = {r}) (hab : (gateAt C r).inputs = [a, b])
    {A B S T : Finset (Fin n)} (hA : RawForm C r a A false) (hB : RawForm C r b B false)
    (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and) (hc : BelowF G C j)
    (hpq : (gateAt C j).inputs = [p, q] ∨ (gateAt C j).inputs = [q, p])
    (hP : RawForm C r p S true) (hQ : RawForm C r q T false)
    {u v c : Fin n} (huA : u ∈ A) (huB : u ∈ B) (hvA : v ∈ A) (hvB : v ∈ B)
    (hne : u ≠ v) (huc : G.Adj u c) (hvc : G.Adj v c) : q = c.val := by
  obtain ⟨hr, hrand, _⟩ := junkMember G C hJ
  have hprod := originalJunkProduct h.1 hr hrand hab hA hB
  have ht : OrientedTop C r j S T true := by
    intro V hV x
    have hd := cleanDifferent G C hJ hc
    rcases hpq with he | he
    · rw [evalExcept_and hV hj hd hand he x, hP.2 V hV x, hQ.2 V hV x]
      simp [hits]
    · rw [evalExcept_and hV hj hd hand he x, hP.2 V hV x, hQ.2 V hV x]
      simp [hits, and_comm]
  have hm : q ∈ (gateAt C j).inputs := by rcases hpq with he | he <;> simp [he]
  have hbnd := h.1.2.1 j hj q hm
  let V := fun (x : Fin n → Bool) w => val C (List.ofFn x) w
  have hV : EvalExcept n C r V := originalEvalExcept h.1 r
  have hsem (x : Fin n → Bool) : V x q = true ↔ hits T x := by simpa [hits] using hQ.2 V hV x
  have hcentre (x : Fin n → Bool) (hx : hits T x) : x c = true :=
    overlapCarrierCentre G h.1 h4 hprod hc ht huA huB hvA hvB hne huc hvc x hx
  have hcT : c ∈ T := by
    obtain ⟨d, hd, _⟩ := (hsem (fun _ => true)).mp (allTrueWires h.1 q (by omega))
    have hcd : c = d := by simpa using hcentre (fun w => decide (w = d)) ⟨d, hd, by simp⟩
    exact hcd.symm ▸ hd
  have heq (x : Fin n → Bool) : V x q = x c := by
    apply Bool.eq_iff_iff.mpr
    exact (hsem x).trans ⟨hcentre x, fun hx => ⟨c, hcT, hx⟩⟩
  by_cases hq : q < n
  · let z : Fin n := ⟨q, hq⟩
    have he := (hV.1 (fun w => decide (w = c)) z).symm.trans (heq (fun w => decide (w = c)))
    have hzc : z = c := by simpa using he
    exact congrArg Fin.val hzc
  · obtain ⟨k, rfl⟩ : ∃ k, q = n + k := ⟨q - n, by omega⟩
    have hcn := c.isLt
    apply False.elim
    apply noEqualEarlier G C h k c.val (by omega) (by omega)
    intro x
    exact (heq x).trans (hV.1 x c).symm

private lemma noBypassPreserving {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r)
    (he : ∀ x : Fin n → Bool, (bypass n C r i).eval (List.ofFn x) = true ↔
      graphFun G ∅ x = true) : False := by
  have hao : IsAO2 n (bypass n C r i) := by
    rw [← erase_eq_bypass n C r i hr]
    exact erase_exactAO h.1 hr hi
  have hf : circuitFun n (bypass n C r i) = graphFun G ∅ := by
    funext x
    exact Bool.eq_iff_iff.mpr (he x)
  have hm := h.2.2 _ hao hf
  have hs : (bypass n C r i).size = C.gates.length - 1 := bypass_length n C r i
  change C.gates.length ≤ (bypass n C r i).size at hm
  omega

/-- At least one clean top can carry the unique junk in its oriented form.
    Otherwise redirecting the junk to any earlier raw input changes no top. -/
private lemma someCarrier {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    {r : ℕ} (hJ : junk G C = {r}) (u : Fin n) :
    ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧ BelowF G C j ∧
      ∃ S T : Finset (Fin n), OrientedTop C r j S T true := by
  by_contra hn
  have hr := (junkMember G C hJ).1
  have hi : u.val < n + r := by have := u.isLt; omega
  let V := fun (x : Fin n → Bool) w => val C (List.ofFn x) w
  let W := fun (x : Fin n → Bool) w =>
    val (bypass n C r u.val) (List.ofFn x) (aliasWire (n + r) u.val w)
  have hV : EvalExcept n C r V := originalEvalExcept h.1 r
  have hW : EvalExcept n C r W := bypassEvalExcept h.1 hr hi
  have htop (x : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length)
      (ho : (gateAt C j).op = GateOp.and) (hc : BelowF G C j) :
      W x (n + j) = true ↔ V x (n + j) = true := by
    obtain ⟨S, T, f, ht⟩ := orientedTop G C h hl hJ hj ho hc
    cases f with
    | false => rw [ht W hW x, ht V hV x]; simp
    | true => exact (hn ⟨j, hj, ho, hc, S, T, ht⟩).elim
  apply noBypassPreserving G C h hr hi
  intro x
  change W x C.output = true ↔ _
  have hv : V x C.output = graphFun G ∅ x := congrFun h.2.1 x
  rw [← hv, collectorSemantics G C h hl hJ hW x, collectorSemantics G C h hl hJ hV x]
  exact exists_congr (fun j => and_congr_right (fun hj => and_congr_right (fun ho =>
    and_congr_right (fun hc => htop x j hj ho hc))))

private lemma overlapCentreExists {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C) (h4 : NoFourCycle G)
    {r : ℕ} (hJ : junk G C = {r}) {A B : Finset (Fin n)}
    (hprod : ∀ x : Fin n → Bool, val C (List.ofFn x) (n + r) = true ↔ hits A x ∧ hits B x)
    {u v : Fin n} (huA : u ∈ A) (huB : u ∈ B) (hvA : v ∈ A) (hvB : v ∈ B) (hne : u ≠ v) :
    ∃! c : Fin n, G.Adj u c ∧ G.Adj v c := by
  obtain ⟨j, hj, _, hc, S, T, ht⟩ := someCarrier G C h hl hJ u
  let x : Fin n → Bool := fun _ => true
  have hv : val C (List.ofFn x) (n + j) = true := allTrueWires h.1 _ (by omega)
  obtain ⟨c, hcT, _⟩ := ((ht _ (originalEvalExcept h.1 r) x).mp hv).2
  have huc := carrierCross G h.1 hprod hc ht huA huB hcT (Or.inl rfl) (Or.inl rfl)
  have hvc := carrierCross G h.1 hprod hc ht hvA hvB hcT (Or.inl rfl) (Or.inl rfl)
  exact ⟨c, ⟨huc, hvc⟩, fun d hd => commonNeighborUnique G h4 hne huc hvc hd.1 hd.2⟩

/-- Two distinct shared raw vertices force a unique common centre. -/
theorem twoOverlapCommonCentre {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C) (h4 : NoFourCycle G)
    {r a b : ℕ} (hJ : junk G C = {r}) (hab : (gateAt C r).inputs = [a, b])
    {A B : Finset (Fin n)} (hA : RawForm C r a A false) (hB : RawForm C r b B false)
    {u v : Fin n} (huA : u ∈ A) (huB : u ∈ B) (hvA : v ∈ A) (hvB : v ∈ B)
    (hne : u ≠ v) : ∃! c : Fin n, G.Adj u c ∧ G.Adj v c := by
  obtain ⟨hr, hand, _⟩ := junkMember G C hJ
  exact overlapCentreExists G C h hl h4 hJ (originalJunkProduct h.1 hr hand hab hA hB)
    huA huB hvA hvB hne

private lemma exposureCleansProvider {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C) (h4 : NoFourCycle G)
    {r : ℕ} (hJ : junk G C = {r}) {A B : Finset (Fin n)}
    (hprod : ∀ x : Fin n → Bool, val C (List.ofFn x) (n + r) = true ↔ hits A x ∧ hits B x)
    {u v c : Fin n} (huA : u ∈ A) (huB : u ∈ B) (hvA : v ∈ A) (hvB : v ∈ B)
    (hne : u ≠ v) (huc : G.Adj u c) (hvc : G.Adj v c) (hcA : c ∈ A) :
    ∀ b ∈ B, G.Adj c b := by
  obtain ⟨j, hj, _, hc, S, T, ht⟩ := someCarrier G C h hl hJ u
  let x : Fin n → Bool := fun _ => true
  have hw : val C (List.ofFn x) (n + j) = true := allTrueWires h.1 _ (by omega)
  obtain ⟨d, hd, _⟩ := ((ht _ (originalEvalExcept h.1 r) x).mp hw).2
  have hud := carrierCross G h.1 hprod hc ht huA huB hd (Or.inl rfl) (Or.inl rfl)
  have hvd := carrierCross G h.1 hprod hc ht hvA hvB hd (Or.inl rfl) (Or.inl rfl)
  have he := commonNeighborUnique G h4 hne huc hvc hud hvd
  subst d
  intro b hb
  exact (G.adj_comm b c).mp (carrierCross G h.1 hprod hc ht hcA hb hd (Or.inr rfl) (Or.inl rfl))

/-- A filtered replacement at the junk wire accepts no false input and
    preserves every edge input. The two conclusions are sufficient for any
    concrete monotone circuit that implements this redirected valuation. -/
private theorem overlapRedirect {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C) (h4 : NoFourCycle G)
    {r : ℕ} (hJ : junk G C = {r}) {A B : Finset (Fin n)}
    (hprod : ∀ x : Fin n → Bool, val C (List.ofFn x) (n + r) = true ↔ hits A x ∧ hits B x)
    {u v c : Fin n} (huA : u ∈ A) (huB : u ∈ B) (hvA : v ∈ A) (hvB : v ∈ B)
    (hne : u ≠ v) (huc : G.Adj u c) (hvc : G.Adj v c)
    {R : Finset (Fin n)} (hR : R = A ∨ R = B) (hcR : c ∉ R)
    {W : (Fin n → Bool) → ℕ → Bool} (hW : EvalExcept n C r W)
    (hfill : ∀ x : Fin n → Bool, W x (n + r) = true ↔ hits (R.filter (G.Adj c)) x) :
    (∀ x : Fin n → Bool, W x C.output = true → graphFun G ∅ x = true) ∧
      ∀ a b : Fin n, G.Adj a b → W (pairInput a b) C.output = true := by
  let V := fun (x : Fin n → Bool) w => val C (List.ofFn x) w
  have hV : EvalExcept n C r V := originalEvalExcept h.1 r
  have hcentre (j : ℕ) (hc : BelowF G C j) (S T : Finset (Fin n))
      (ht : OrientedTop C r j S T true) (x : Fin n → Bool) (hx : hits T x) : x c = true :=
    overlapCarrierCentre G h.1 h4 hprod hc ht huA huB hvA hvB hne huc hvc x hx
  constructor
  · intro x hx
    obtain ⟨j, hj, ho, hc, hjx⟩ := (collectorSemantics G C h hl hJ hW x).mp hx
    obtain ⟨S, T, f, ht⟩ := orientedTop G C h hl hJ hj ho hc
    obtain ⟨hs, htx⟩ := (ht W hW x).mp hjx
    rcases hs with hs | ⟨hf, hw⟩
    · exact hc x ((ht V hV x).mpr ⟨Or.inl hs, htx⟩)
    · subst f
      obtain ⟨b, hb, hbx⟩ := (hfill x).mp hw
      exact (graph_true G x).mpr ⟨c, b, (Finset.mem_filter.mp hb).2,
        hcentre j hc S T ht x htx, hbx⟩
  · intro a b hab
    let x := pairInput a b
    have hx : V x C.output = true := (congrFun h.2.1 x).trans (pair_true G a b hab)
    obtain ⟨j, hj, ho, hc, hjx⟩ := (collectorSemantics G C h hl hJ hV x).mp hx
    obtain ⟨S, T, f, ht⟩ := orientedTop G C h hl hJ hj ho hc
    obtain ⟨hs, htx⟩ := (ht V hV x).mp hjx
    apply (collectorSemantics G C h hl hJ hW x).mpr
    refine ⟨j, hj, ho, hc, (ht W hW x).mpr ⟨?_, htx⟩⟩
    rcases hs with hs | ⟨hf, hv⟩
    · exact Or.inl hs
    · subst f
      have hcx : x c = true := hcentre j hc S T ht x htx
      have hcab : c = a ∨ c = b := by simpa [x, pairInput] using hcx
      have hv' : hits A x ∧ hits B x := (hprod x).mp hv
      have hrx : hits R x := by rcases hR with rfl | rfl; exacts [hv'.1, hv'.2]
      obtain ⟨d, hd, hdx⟩ := hrx
      have hdab : d = a ∨ d = b := by simpa [x, pairInput] using hdx
      have hdc : d ≠ c := fun he => hcR (he ▸ hd)
      have hcd : G.Adj c d := by
        rcases hcab with rfl | rfl <;> rcases hdab with rfl | rfl
        · exact (hdc rfl).elim
        · exact hab
        · exact (G.adj_comm _ _).mp hab
        · exact (hdc rfl).elim
      exact Or.inr ⟨rfl, (hfill x).mpr ⟨d, Finset.mem_filter.mpr ⟨hd, hcd⟩, hdx⟩⟩

/-- A rebuilt circuit contradicts leastness if it implements the filtered
    redirection at the output and uses strictly fewer original gate units. -/
theorem noTwoOverlapWithRebuiltFilter {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C) (h4 : NoFourCycle G)
    {r a b : ℕ} (hJ : junk G C = {r}) (hab : (gateAt C r).inputs = [a, b])
    {A B : Finset (Fin n)} (hA : RawForm C r a A false) (hB : RawForm C r b B false)
    {u v c : Fin n} (huA : u ∈ A) (huB : u ∈ B) (hvA : v ∈ A) (hvB : v ∈ B)
    (hne : u ≠ v) (huc : G.Adj u c) (hvc : G.Adj v c)
    {R : Finset (Fin n)} (hR : R = A ∨ R = B) (hcR : c ∉ R)
    (D : Circuit) (hD : IsAO2 n D) (hsize : D.size < C.size)
    {W : (Fin n → Bool) → ℕ → Bool} (hW : EvalExcept n C r W)
    (hfill : ∀ x, W x (n + r) = true ↔ ∃ d ∈ R.filter (G.Adj c), x d = true)
    (hout : ∀ x, D.eval (List.ofFn x) = W x C.output) : False := by
  obtain ⟨hr, hand, _⟩ := junkMember G C hJ
  have hprod := originalJunkProduct h.1 hr hand hab hA hB
  obtain ⟨hneg, hedge⟩ := overlapRedirect G C h hl h4 hJ hprod huA huB hvA hvB hne huc hvc
    hR hcR hW hfill
  have heq : circuitFun n D = graphFun G ∅ := by
    funext x
    apply Bool.eq_iff_iff.mpr
    change D.eval (List.ofFn x) = true ↔ _
    constructor
    · rw [hout x]
      exact hneg x
    · intro hx
      obtain ⟨d, e, hde, hd, he⟩ := (graph_true G x).mp hx
      have hedgeD : D.eval (List.ofFn (pairInput d e)) = true := (hout _).trans (hedge d e hde)
      apply circuit_monotone n D (ao_mono hD) (pairInput d e) x ?_ hedgeD
      intro w hw
      have hw' : w = d ∨ w = e := by simpa [pairInput] using hw
      rcases hw' with rfl | rfl
      · exact hd
      · exact he
  exact (Nat.not_lt_of_ge (h.2.2 D hD heq)) hsize

/-- An earlier wire realizing the chosen filtered provider suffices to
    strictly delete the unique junk in the multiple-overlap case. -/
theorem noTwoOverlapWithEarlierFilter {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C) (h4 : NoFourCycle G)
    {r a b : ℕ} (hJ : junk G C = {r}) (hab : (gateAt C r).inputs = [a, b])
    {A B : Finset (Fin n)} (hA : RawForm C r a A false) (hB : RawForm C r b B false)
    {u v c : Fin n} (huA : u ∈ A) (huB : u ∈ B) (hvA : v ∈ A) (hvB : v ∈ B)
    (hne : u ≠ v) (huc : G.Adj u c) (hvc : G.Adj v c)
    {i : ℕ} {R : Finset (Fin n)} (hi : i < n + r) (hR : R = A ∨ R = B)
    (hcR : c ∉ R) (hraw : RawForm C r i (R.filter (G.Adj c)) false) : False := by
  have hr := (junkMember G C hJ).1
  let D := bypass n C r i
  let W := fun (x : Fin n → Bool) w => val D (List.ofFn x) (aliasWire (n + r) i w)
  have hW : EvalExcept n C r W := bypassEvalExcept h.1 hr hi
  have hfill (x : Fin n → Bool) : W x (n + r) = true ↔ hits (R.filter (G.Adj c)) x := by
    have hw : W x (n + r) = W x i := by simp [W, aliasWire, Nat.ne_of_lt hi, Nat.not_lt_of_ge hi.le]
    rw [hw]
    simpa [hits] using hraw.2 W hW x
  have hD : IsAO2 n D := by
    change IsAO2 n (bypass n C r i)
    rw [← erase_eq_bypass n C r i hr]
    exact erase_exactAO h.1 hr hi
  have hsize : D.size < C.size := by
    change (bypass n C r i).gates.length < C.gates.length
    rw [bypass_length]
    omega
  exact noTwoOverlapWithRebuiltFilter G C h hl h4 hJ hab hA hB huA huB hvA hvB hne huc hvc
    hR hcR D hD hsize hW hfill (fun _ => rfl)

/-- When the common centre is exposed, the opposite operand already
    realizes the filtered provider. -/
theorem noExposedTwoOverlap {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C) (h4 : NoFourCycle G)
    {r a b : ℕ} (hJ : junk G C = {r}) (hab : (gateAt C r).inputs = [a, b])
    {A B : Finset (Fin n)} (hA : RawForm C r a A false) (hB : RawForm C r b B false)
    {u v c : Fin n} (huA : u ∈ A) (huB : u ∈ B) (hvA : v ∈ A) (hvB : v ∈ B)
    (hne : u ≠ v) (huc : G.Adj u c) (hvc : G.Adj v c) (hc : c ∈ A ∨ c ∈ B) : False := by
  obtain ⟨hr, hand, _⟩ := junkMember G C hJ
  have hprod := originalJunkProduct h.1 hr hand hab hA hB
  have trim (i : ℕ) (R : Finset (Fin n)) (hi : i < n + r)
      (hR : R = A ∨ R = B) (hraw : RawForm C r i R false) (hclean : ∀ d ∈ R, G.Adj c d) : False := by
    have hcR : c ∉ R := fun hm => G.ne_of_adj (hclean c hm) rfl
    have hf : R.filter (G.Adj c) = R := Finset.filter_true_of_mem hclean
    exact noTwoOverlapWithEarlierFilter G C h hl h4 hJ hab hA hB huA huB hvA hvB hne huc hvc
      hi hR hcR (hf.symm ▸ hraw)
  rcases hc with hcA | hcB
  · exact trim b B (h.1.2.1 r hr b (by rw [hab]; simp)) (Or.inr rfl) hB
      (exposureCleansProvider G C h hl h4 hJ hprod huA huB hvA hvB hne huc hvc hcA)
  · have hswap (x : Fin n → Bool) : val C (List.ofFn x) (n + r) = true ↔ hits B x ∧ hits A x := by
      rw [hprod x, and_comm]
    exact trim a A (h.1.2.1 r hr a (by rw [hab]; simp)) (Or.inl rfl) hA
      (exposureCleansProvider G C h hl h4 hJ hswap huB huA hvB hvA hne huc hvc hcB)

#print axioms twoOverlapCommonCentre
#print axioms twoOverlapOppositeRaw
#print axioms overlapRedirect
#print axioms noTwoOverlapWithRebuiltFilter
#print axioms noTwoOverlapWithEarlierFilter
#print axioms noExposedTwoOverlap

private def WireAvailable {n : ℕ} (D : Circuit) (f : (Fin n → Bool) → Bool) : Prop :=
  (∀ x, f x = false) ∨ ∃ w < n + D.gates.length, ∀ x, val D (List.ofFn x) w = f x

private def PreservesWires (n : ℕ) (D E : Circuit) : Prop :=
  D.gates.length ≤ E.gates.length ∧
    ∀ (x : Fin n → Bool) w, w < n + D.gates.length → val E (List.ofFn x) w = val D (List.ofFn x) w

private lemma wireAvailablePreserved {n : ℕ} {D E : Circuit} (h : PreservesWires n D E)
    {f : (Fin n → Bool) → Bool} (hf : WireAvailable D f) : WireAvailable E f := by
  rcases hf with hz | ⟨w, hw, he⟩
  · exact Or.inl hz
  · exact Or.inr ⟨w, by have := h.1; omega, fun x => (h.2 x w hw).trans (he x)⟩

private lemma appendAvailableOr {n : ℕ} (D : Circuit) (hD : IsAO2 n D)
    {f g : (Fin n → Bool) → Bool} (hf : WireAvailable D f) (hg : WireAvailable D g) :
    ∃ E, IsAO2 n E ∧ PreservesWires n D E ∧ E.gates.length ≤ D.gates.length + 1 ∧
      ((∀ x, f x = false) ∨ (∀ x, g x = false) → E.gates.length ≤ D.gates.length) ∧
      WireAvailable E (fun x => f x || g x) := by
  have hself : PreservesWires n D D := ⟨le_rfl, fun _ _ _ => rfl⟩
  rcases hf with hf | ⟨a, ha, hfa⟩
  · have he : (fun x => f x || g x) = g := funext fun x => by simp [hf x]
    exact ⟨D, hD, hself, by omega, fun _ => le_rfl, he.symm ▸ hg⟩
  · rcases hg with hg | ⟨b, hb, hgb⟩
    · have he : (fun x => f x || g x) = f := funext fun x => by simp [hg x]
      exact ⟨D, hD, hself, by omega, fun _ => le_rfl, he.symm ▸ Or.inr ⟨a, ha, hfa⟩⟩
    · obtain ⟨hlen, hE, hkeep, hval⟩ := appendBinary_spec hD (Or.inr rfl) ha hb
      refine ⟨appendBinary D GateOp.or a b, hE, ⟨by omega, hkeep⟩, by omega, ?_, Or.inr ?_⟩
      · rintro (hf | hg)
        · have ht : f (fun _ => true) = true := (hfa _).symm.trans (allTrueWires hD a ha)
          cases (hf _).symm.trans ht
        · have ht : g (fun _ => true) = true := (hgb _).symm.trans (allTrueWires hD b hb)
          cases (hg _).symm.trans ht
      · refine ⟨n + D.gates.length, by omega, fun x => ?_⟩
        rw [hval x, hfa x, hgb x]
        simp [GateOp.eval]

/-- Extend a protected prefix with filtered values. An OR with a known
    false input can be excluded from the count of appended gates. -/
private theorem compileAvailablePrefixBudget {n : ℕ} (C D : Circuit) (hC : IsAO2 n C) (hD : IsAO2 n D)
    (r : ℕ) (hr : r ≤ C.gates.length) (keep : ℕ → Prop) [DecidablePred keep]
    (free : ℕ → Prop) [DecidablePred free]
    (needed : ℕ → Prop) (V : (Fin n → Bool) → ℕ → Bool)
    (raw : ∀ w < n, needed w → WireAvailable D (fun x => V x w))
    (retained : ∀ j < r, keep j → needed (n + j) → WireAvailable D (fun x => V x (n + j)))
    (skipped : ∀ j < r, ¬ keep j → needed (n + j) →
      (∀ w ∈ (gateAt C j).inputs, needed w) ∧
      (∀ x, V x (n + j) = true ↔ ∃ w ∈ (gateAt C j).inputs, V x w = true))
    (freeInput : ∀ j < r, ¬ keep j → needed (n + j) → free j →
      ∃ w ∈ (gateAt C j).inputs, ∀ x, V x w = false) :
    ∃ E, IsAO2 n E ∧ PreservesWires n D E ∧
      E.gates.length ≤ D.gates.length + ((Finset.range r).filter fun j => ¬ keep j ∧ ¬ free j).card ∧
      ∀ w < n + r, needed w → WireAvailable E (fun x => V x w) := by
  classical
  have main : ∀ k ≤ r, ∃ E, IsAO2 n E ∧ PreservesWires n D E ∧
      E.gates.length ≤ D.gates.length + ((Finset.range k).filter fun j => ¬ keep j ∧ ¬ free j).card ∧
      ∀ w < n + k, needed w → WireAvailable E (fun x => V x w) := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨D, hD, ⟨le_rfl, fun _ _ _ => rfl⟩, by simp, fun w hw hn => raw w (by omega) hn⟩
    | succ k ih =>
      intro hk
      obtain ⟨E, hE, hDE, hcount, hprev⟩ := ih (by omega)
      have hj : k < C.gates.length := by omega
      have hmono : ((Finset.range k).filter fun j => ¬ keep j ∧ ¬ free j).card ≤
          ((Finset.range (k + 1)).filter fun j => ¬ keep j ∧ ¬ free j).card := by
        apply Finset.card_le_card
        exact Finset.filter_subset_filter _ (Finset.range_mono (Nat.le_succ k))
      by_cases hn : needed (n + k)
      · by_cases hp : keep k
        · refine ⟨E, hE, hDE, by omega, fun w hw hwneed => ?_⟩
          by_cases he : w = n + k
          · subst w
            exact wireAvailablePreserved hDE (retained k (by omega) hp hn)
          · exact hprev w (by omega) hwneed
        · obtain ⟨a, b, hab⟩ := twoOperands hC hj
          have hma : a ∈ (gateAt C k).inputs := by rw [hab]; simp
          have hmb : b ∈ (gateAt C k).inputs := by rw [hab]; simp
          obtain ⟨hneed, hor⟩ := skipped k (by omega) hp hn
          have ha := hprev a (hC.2.1 k hj a hma) (hneed a hma)
          have hb := hprev b (hC.2.1 k hj b hmb) (hneed b hmb)
          obtain ⟨F, hF, hEF, hlen, hfree, hf⟩ := appendAvailableOr E hE ha hb
          have hDF : PreservesWires n D F := ⟨hDE.1.trans hEF.1, fun x w hw =>
            (hEF.2 x w (by have := hDE.1; omega)).trans (hDE.2 x w hw)⟩
          have hbudget : F.gates.length ≤ D.gates.length +
              ((Finset.range (k + 1)).filter fun j => ¬ keep j ∧ ¬ free j).card := by
            by_cases hz : free k
            · obtain ⟨w, hw, hzero⟩ := freeInput k (by omega) hp hn hz
              have he : w = a ∨ w = b := by simpa [hab] using hw
              have hlen' := hfree (by rcases he with rfl | rfl; exacts [Or.inl hzero, Or.inr hzero])
              omega
            · have hcard : ((Finset.range (k + 1)).filter fun j => ¬ keep j ∧ ¬ free j).card =
                  ((Finset.range k).filter fun j => ¬ keep j ∧ ¬ free j).card + 1 := by
                rw [Finset.range_add_one, Finset.filter_insert, ite_eq_left ⟨hp, hz⟩,
                  Finset.card_insert_of_notMem (by simp)]
              omega
          refine ⟨F, hF, hDF, hbudget, fun w hw hwneed => ?_⟩
          by_cases he : w = n + k
          · subst w
            have heq : (fun x => V x a || V x b) = fun x => V x (n + k) := by
              funext x
              apply Bool.eq_iff_iff.mpr
              rw [hor x, hab]
              simp
            exact heq ▸ hf
          · exact wireAvailablePreserved hEF (hprev w (by omega) hwneed)
      · refine ⟨E, hE, hDE, by omega, fun w hw hwneed => ?_⟩
        have hne : w ≠ n + k := fun he => hn (he ▸ hwneed)
        exact hprev w (by omega) hwneed
  exact main r le_rfl

private theorem compileAvailablePrefix {n : ℕ} (C D : Circuit) (hC : IsAO2 n C) (hD : IsAO2 n D)
    (r : ℕ) (hr : r ≤ C.gates.length) (keep : ℕ → Prop) [DecidablePred keep]
    (needed : ℕ → Prop) (V : (Fin n → Bool) → ℕ → Bool)
    (raw : ∀ w < n, needed w → WireAvailable D (fun x => V x w))
    (retained : ∀ j < r, keep j → needed (n + j) → WireAvailable D (fun x => V x (n + j)))
    (skipped : ∀ j < r, ¬ keep j → needed (n + j) →
      (∀ w ∈ (gateAt C j).inputs, needed w) ∧
      ∀ x, V x (n + j) = true ↔ ∃ w ∈ (gateAt C j).inputs, V x w = true) :
    ∃ E, IsAO2 n E ∧ PreservesWires n D E ∧
      E.gates.length ≤ D.gates.length + ((Finset.range r).filter fun j => ¬ keep j).card ∧
      ∀ w < n + r, needed w → WireAvailable E (fun x => V x w) := by
  simpa using compileAvailablePrefixBudget C D hC hD r hr keep (fun _ => False) needed V
    raw retained skipped (fun _ _ _ _ hf => hf.elim)

#print axioms compileAvailablePrefixBudget
#print axioms compileAvailablePrefix

private def neighbourhoodInput {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (c : Fin n) (x : Fin n → Bool) (d : Fin n) : Bool :=
  if G.Adj c d then x d else false

private lemma hitsNeighbourhoodInput {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (c : Fin n) (x : Fin n → Bool) (S : Finset (Fin n)) :
    hits S (neighbourhoodInput G c x) ↔ hits (S.filter (G.Adj c)) x := by
  constructor
  · rintro ⟨v, hv, hx⟩
    by_cases ha : G.Adj c v
    · exact ⟨v, Finset.mem_filter.mpr ⟨hv, ha⟩, by simpa [neighbourhoodInput, ha] using hx⟩
    · simp [neighbourhoodInput, ha] at hx
  · rintro ⟨v, hv, hx⟩
    obtain ⟨hv, ha⟩ := Finset.mem_filter.mp hv
    exact ⟨v, hv, by simpa [neighbourhoodInput, ha] using hx⟩

private lemma pureProviderValue {n : ℕ} {C : Circuit} (hC : IsAO2 n C)
    {r w : ℕ} {S : Finset (Fin n)} (hS : RawForm C r w S false) (x : Fin n → Bool) :
    val C (List.ofFn x) w = true ↔ hits S x := by
  simpa [hits] using hS.2 _ (originalEvalExcept hC r) x

/-- A protected raw OR contained in one neighbourhood can supply its
    filtered value using its existing wire, a raw alias, or false. -/
private lemma protectedFilteredAvailable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) {C D : Circuit} (hC : IsAO2 n C)
    {r w i : ℕ} {S : Finset (Fin n)} (hS : RawForm C r w S false)
    (hi : i < n + D.gates.length) (he : ∀ x : Fin n → Bool, val D (List.ofFn x) i = val C (List.ofFn x) w)
    (c d : Fin n) (hd : ∀ v ∈ S, G.Adj d v) :
    WireAvailable D (fun x => val C (List.ofFn (neighbourhoodInput G c x)) w) := by
  let T := S.filter (G.Adj c)
  have hf (x : Fin n → Bool) : val C (List.ofFn (neighbourhoodInput G c x)) w = true ↔ hits T x :=
    (pureProviderValue hC hS _).trans (hitsNeighbourhoodInput G c x S)
  by_cases hcd : c = d
  · subst d
    refine Or.inr ⟨i, hi, fun x => ?_⟩
    apply Bool.eq_iff_iff.mpr
    rw [he x, pureProviderValue hC hS, hf]
    rw [show T = S from Finset.filter_true_of_mem hd]
  · have hnum : T.card ≤ 1 := by
      apply (Finset.card_le_card ?_).trans (h4 c d hcd)
      intro v hv
      obtain ⟨hs, hc⟩ := Finset.mem_filter.mp hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc, hd v hs⟩
    by_cases hT : T.Nonempty
    · obtain ⟨v, hv⟩ := hT
      have ht : T = {v} := by
        apply Finset.Subset.antisymm
        · intro u hu
          exact Finset.mem_singleton.mpr (Finset.card_le_one.mp hnum u hu v hv)
        · exact Finset.singleton_subset_iff.mpr hv
      refine Or.inr ⟨v.val, by have := v.isLt; omega, fun x => ?_⟩
      apply Bool.eq_iff_iff.mpr
      rw [hf x, ht]
      rw [val_input (n := n) (by simp) v.isLt]
      simp [hits, List.getD_eq_getElem?_getD, v.isLt]
    · apply Or.inl
      intro x
      change val C (List.ofFn (neighbourhoodInput G c x)) w = false
      cases hx : val C (List.ofFn (neighbourhoodInput G c x)) w
      · rfl
      · obtain ⟨v, hv, _⟩ := (hf x).mp hx
        exact (hT ⟨v, hv⟩).elim

/-- A wire has a path to the output whose gates after that wire omit the junk. -/
inductive AvoidJunk (n : ℕ) (C : Circuit) (r : ℕ) : ℕ → Prop where
  | output : AvoidJunk n C r C.output
  | input {j w : ℕ} (hj : j < C.gates.length) (hne : j ≠ r)
      (hw : w ∈ (gateAt C j).inputs) : AvoidJunk n C r (n + j) → AvoidJunk n C r w

/-- Every real gate either has a use avoiding the junk or is an ancestor of
    the junk. The latter case covers a pre-junk gate with no protected use. -/
theorem avoidJunkOrAncestor {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) {r : ℕ} (hr : r < C.gates.length) :
    ∀ j < C.gates.length, AvoidJunk n C r (n + j) ∨ InCone n C j r := by
  have main : ∀ d : ℕ, ∀ j < C.gates.length, C.gates.length - j = d →
      AvoidJunk n C r (n + j) ∨ InCone n C j r := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro j hj hd
      by_cases ho : C.output = n + j
      · rw [← ho]
        exact Or.inl .output
      · obtain ⟨a, b, hab⟩ := twoOperands h.1 hj
        have ha := h.1.2.1 j hj a (by rw [hab]; simp)
        obtain ⟨k, hjk, hk, hm⟩ := noUnreadGate G C h j a hj ha ho
        have hstep : InCone n C j k := (coneRec hk j).mpr
          ⟨n + j, hm, by omega, by omega, Or.inl (by omega)⟩
        by_cases he : k = r
        · exact Or.inr (he ▸ hstep)
        · rcases ih (C.gates.length - k) (by omega) k hk rfl with hav | hcr
          · exact Or.inl (.input hk he hm hav)
          · exact Or.inr (coneTrans _ hr _ _ hstep hcr)
  intro j hj
  exact main _ j hj rfl

theorem avoidJunkOfGe {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) {r j : ℕ} (hr : r ≤ j)
    (hj : j < C.gates.length) : AvoidJunk n C r (n + j) := by
  rcases avoidJunkOrAncestor G C h (by omega : r < C.gates.length) j hj with he | hc
  · exact he
  · have hlt := conePrecedes r (by omega : r < C.gates.length) j hc
    omega

/-- From a clean gate, every immediate reader is clean and hence differs
    from the unique junk. Following readers therefore gives a protected use. -/
theorem cleanGateAvoidJunk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    {r : ℕ} (hJ : junk G C = {r}) :
    ∀ j < C.gates.length, BelowF G C j → AvoidJunk n C r (n + j) := by
  have main : ∀ d : ℕ, ∀ j < C.gates.length, C.gates.length - j = d →
      BelowF G C j → AvoidJunk n C r (n + j) := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro j hj hd hc
      by_cases ho : C.output = n + j
      · rw [← ho]
        exact .output
      · obtain ⟨a, b, hab⟩ := twoOperands h.1 hj
        have ha := h.1.2.1 j hj a (by rw [hab]; simp)
        obtain ⟨k, hjk, hk, hm⟩ := noUnreadGate G C h j a hj ha ho
        have hkc := (cleanWireReader G C h hl hk hm ((cleanWireGate G C j).mpr hc)).2
        exact .input hk (cleanDifferent G C hJ hkc) hm
          (ih (C.gates.length - k) (by omega) k hk rfl hkc)
  intro j hj hc
  exact main _ j hj rfl hc

theorem unprotectedPreJunkDirtyOr {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    {r j : ℕ} (hJ : junk G C = {r}) (hj : j < r) (hu : ¬ AvoidJunk n C r (n + j)) :
    (gateAt C j).op = GateOp.or ∧ ¬ BelowF G C j := by
  have hr := (junkMember G C hJ).1
  have hj' : j < C.gates.length := hj.trans hr
  have hd : ¬ BelowF G C j := fun hc => hu (cleanGateAvoidJunk G C h hl hJ _ hj' hc)
  rcases h.1.1 _ (gateAt_mem hj') with hand | hor
  · exact (hj.ne (uniqueDirtyAnd G C hJ hj' hd hand)).elim
  · exact ⟨hor, hd⟩

theorem preJunkDirtyRaw {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    {r w : ℕ} (hJ : junk G C = {r}) (hw : w < n + r) (hd : ¬ CleanWire G C w) :
    ∃ R : Finset (Fin n), RawForm C r w R false := by
  have hr := (junkMember G C hJ).1
  obtain ⟨R, b, hR⟩ := dirtyRawForm G C h hl hJ w (by omega) hd
  cases b with
  | false => exact ⟨R, hR⟩
  | true => exact (not_le_of_gt hw (hR.1 rfl)).elim

theorem protectedSupportNeighbour {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C) (h4 : NoFourCycle G)
    {r a b : ℕ} (hJ : junk G C = {r}) (hab : (gateAt C r).inputs = [a, b])
    {A B : Finset (Fin n)} (hA : RawForm C r a A false) (hB : RawForm C r b B false)
    {u v c : Fin n} (huA : u ∈ A) (huB : u ∈ B) (hvA : v ∈ A) (hvB : v ∈ B)
    (hne : u ≠ v) (huc : G.Adj u c) (hvc : G.Adj v c) {R : Finset (Fin n)}
    {w : ℕ} (hp : AvoidJunk n C r w) (hw : n ≤ w) (hdirty : ¬ CleanWire G C w)
    (hforce : ∀ x : Fin n → Bool, (∃ z ∈ R, x z = true) → val C (List.ofFn x) w = true) :
    ∃ d : Fin n, ∀ z ∈ R, G.Adj d z := by
  have hopposite : ∀ {j p q : ℕ} {P Q : Finset (Fin n)} {f g : Bool},
      j < C.gates.length → (gateAt C j).op = GateOp.and → BelowF G C j →
      ((gateAt C j).inputs = [p, q] ∨ (gateAt C j).inputs = [q, p]) →
      RawForm C r p P f → RawForm C r q Q g → (f = false ∨ g = false) →
      n ≤ p →
      (∀ x : Fin n → Bool, (∃ z ∈ R, x z = true) → val C (List.ofFn x) p = true) →
      ∃ d : Fin n, ∀ z ∈ R, G.Adj d z := by
    intro j p q P Q f g hj hand hc hpq hP hQ hn hp hfp
    have hg : g = false := by
      cases g with
      | false => rfl
      | true =>
        obtain hf | hg := hn
        · subst f
          have hr := twoOverlapOppositeRaw G C h h4 hJ hab hA hB hj hand hc hpq.symm
            hQ hP huA huB hvA hvB hne huc hvc
          have hc' := c.isLt
          omega
        · contradiction
    subst g
    have hq : q < n + j := by
      apply h.1.2.1 j hj q
      rcases hpq with he | he <;> simp [he]
    let V := fun (x : Fin n → Bool) k => val C (List.ofFn x) k
    have hV : EvalExcept n C r V := originalEvalExcept h.1 r
    have hsem (x : Fin n → Bool) : V x q = true ↔ ∃ z ∈ Q, x z = true := by
      simpa using hQ.2 V hV x
    have hall : V (fun _ => true) q = true := allTrueWires h.1 q (by omega)
    obtain ⟨d, hd, _⟩ := (hsem _).mp hall
    refine ⟨d, fun z hz => adjOfPair G ?_⟩
    let x := pairInput d z
    have hd' : x d = true := by simp [x, pairInput]
    have hz' : x z = true := by simp [x, pairInput]
    have hpx : V x p = true := hfp x ⟨z, hz, hz'⟩
    have hqx : V x q = true := (hsem x).mpr ⟨d, hd, hd'⟩
    apply hc x
    have hnr := cleanDifferent G C hJ hc
    rcases hpq with he | he
    · exact (evalExcept_and hV hj hnr hand he x).mpr ⟨hpx, hqx⟩
    · exact (evalExcept_and hV hj hnr hand he x).mpr ⟨hqx, hpx⟩
  induction hp with
  | output =>
    exfalso
    apply hdirty
    intro x hx
    exact (congrFun h.2.1 x).symm.trans hx
  | @input j w hj hjr hmem _ ih =>
    rcases h.1.1 _ (gateAt_mem hj) with hand | hor
    · have hc : BelowF G C j := by
        by_contra hd
        exact hjr (uniqueDirtyAnd G C hJ hj hd hand)
      obtain ⟨p, q, P, Q, f, g, he, hP, hQ, hg⟩ := topProduct G C h hl hJ hj hand hc
      have hw' : w = p ∨ w = q := by simpa [he] using hmem
      rcases hw' with rfl | rfl
      · exact hopposite hj hand hc (Or.inl he) hP hQ hg hw hforce
      · exact hopposite hj hand hc (Or.inr he) hQ hP hg.symm hw hforce
    · apply ih (by omega)
      · intro hc
        exact hdirty (cleanOrOperands G C h.1 hj hor hc hmem)
      · intro x hx
        exact (val_or (n := n) (by simp) hj hor).mpr
          ⟨w, hmem, h.1.2.1 j hj w hmem, hforce x hx⟩

theorem protectedPureSupportNeighbour {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C) (h4 : NoFourCycle G)
    {r a b : ℕ} (hJ : junk G C = {r}) (hab : (gateAt C r).inputs = [a, b])
    {A B : Finset (Fin n)} (hA : RawForm C r a A false) (hB : RawForm C r b B false)
    {u v c : Fin n} (huA : u ∈ A) (huB : u ∈ B) (hvA : v ∈ A) (hvB : v ∈ B)
    (hne : u ≠ v) (huc : G.Adj u c) (hvc : G.Adj v c) {R : Finset (Fin n)}
    {w : ℕ} (hp : AvoidJunk n C r w) (hw : n ≤ w) (hdirty : ¬ CleanWire G C w)
    (hR : RawForm C r w R false) : ∃ d : Fin n, ∀ z ∈ R, G.Adj d z := by
  apply protectedSupportNeighbour G C h hl h4 hJ hab hA hB huA huB hvA hvB hne huc hvc hp hw hdirty
  intro x hx
  exact (hR.2 _ (originalEvalExcept h.1 r) x).mpr (Or.inl hx)

#print axioms protectedPureSupportNeighbour
#print axioms avoidJunkOfGe
#print axioms unprotectedPreJunkDirtyOr

/-- Replay the suffix of an original exact circuit into a new prefix that
    already realizes the retained inputs and the replacement signal. -/
private theorem replaySuffix {n : ℕ} (C : Circuit) (hC : IsAO2 n C)
    (P : ℕ → Prop) (start : ℕ) (D : Circuit) (hD : IsAO2 n D)
    (V : (Fin n → Bool) → ℕ → Bool) (ρ : ℕ → ℕ)
    (hbase : ∀ w, RetainedWire n P start w → ρ w < n + D.gates.length ∧
      ∀ x : Fin n → Bool, val D (List.ofFn x) (ρ w) = V x w)
    (hclosed : ∀ j, start ≤ j → j < C.gates.length → ∀ w ∈ (gateAt C j).inputs,
      RetainedWire n P j w)
    (heval : ∀ (x : Fin n → Bool) j, start ≤ j → j < C.gates.length →
      V x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (V x))) :
    ∀ k, start + k ≤ C.gates.length →
      ∃ (E : Circuit) (σ : ℕ → ℕ), IsAO2 n E ∧ E.gates.length = D.gates.length + k ∧
      ∀ w, RetainedWire n P (start + k) w → σ w < n + E.gates.length ∧
        ∀ x : Fin n → Bool, val E (List.ofFn x) (σ w) = V x w := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨D, ρ, hD, by simp, by simpa using hbase⟩
  | succ k ih =>
    intro hk
    obtain ⟨E, σ, hE, hlen, hσ⟩ := ih (by omega)
    let j := start + k
    have hj : j < C.gates.length := by dsimp [j]; omega
    have hs : start ≤ j := by dsimp [j]; omega
    obtain ⟨a, b, hab⟩ := twoOperands hC hj
    have hma : a ∈ (gateAt C j).inputs := by rw [hab]; simp
    have hmb : b ∈ (gateAt C j).inputs := by rw [hab]; simp
    have ha := hσ a (hclosed j hs hj a hma)
    have hb := hσ b (hclosed j hs hj b hmb)
    let op := (gateAt C j).op
    let F := appendBinary E op (σ a) (σ b)
    obtain ⟨hlenF, hF, hold, hnew⟩ := appendBinary_spec hE (hC.1 _ (gateAt_mem hj)) ha.1 hb.1
    change F.gates.length = E.gates.length + 1 at hlenF
    refine ⟨F, fun w => if w = n + j then n + E.gates.length else σ w, hF, by omega, ?_⟩
    intro w hw
    change RetainedWire n P (j + 1) w at hw
    by_cases he : w = n + j
    · subst w
      dsimp only
      rw [ite_eq_left rfl]
      refine ⟨by omega, ?_⟩
      intro x
      rw [hnew x, ha.2 x, hb.2 x, heval x j hs hj, hab]
      rfl
    · dsimp only
      rw [ite_eq_right he]
      have prev : RetainedWire n P j w := by
        rcases hw with hw | ⟨i, hi, hp, rfl⟩
        · exact Or.inl hw
        · exact Or.inr ⟨i, by omega, hp, rfl⟩
      have ht := hσ w prev
      exact ⟨by omega, fun x => (hold x _ ht.1).trans (ht.2 x)⟩

private def suspendedValue {n : ℕ} (C : Circuit) (r : ℕ)
    (fill : (Fin n → Bool) → Bool) (x : Fin n → Bool) (w : ℕ) : Bool :=
  if hw : w < n then x ⟨w, hw⟩
  else if w = n + r then fill x
  else (gateAt C (w - n)).op.eval ((gateAt C (w - n)).inputs.attach.map fun v =>
    if _hv : v.val < w then suspendedValue C r fill x v.val else false)
termination_by w

private lemma suspendedValue_raw {n : ℕ} (C : Circuit) (r : ℕ)
    (fill : (Fin n → Bool) → Bool) (x : Fin n → Bool) (v : Fin n) :
    suspendedValue C r fill x v.val = x v := by
  rw [suspendedValue, dite_eq_left v.isLt]

private lemma suspendedValue_hole {n : ℕ} (C : Circuit) (r : ℕ)
    (fill : (Fin n → Bool) → Bool) (x : Fin n → Bool) :
    suspendedValue C r fill x (n + r) = fill x := by
  rw [suspendedValue, dite_eq_right (by omega), ite_eq_left rfl]

private lemma suspendedValue_evalExcept {n : ℕ} (C : Circuit) (h : IsAO2 n C) (r : ℕ)
    (fill : (Fin n → Bool) → Bool) : EvalExcept n C r (suspendedValue C r fill) := by
  refine ⟨suspendedValue_raw C r fill, ?_⟩
  intro x j hj hne
  rw [suspendedValue, dite_eq_right (by omega), ite_eq_right (by omega), Nat.add_sub_cancel_left]
  congr 1
  conv => rhs; rw [← List.attach_map_val]
  apply List.map_congr_left
  intro v _
  exact dite_eq_left (h.2.1 j hj v.val v.property)

/-- The suspended gate can be assigned any Boolean function while retaining
    all other gate equations. -/
theorem existsEvalExceptWithJunk {n : ℕ} (C : Circuit) (h : IsAO2 n C) (r : ℕ)
    (fill : (Fin n → Bool) → Bool) :
    ∃ V, EvalExcept n C r V ∧ ∀ x, V x (n + r) = fill x :=
  ⟨suspendedValue C r fill, suspendedValue_evalExcept C h r fill, suspendedValue_hole C r fill⟩

#print axioms existsEvalExceptWithJunk

private lemma suspendedValue_before {n : ℕ} (C : Circuit) (h : IsAO2 n C) (r : ℕ)
    (hr : r < C.gates.length) (fill : (Fin n → Bool) → Bool) (x : Fin n → Bool) :
    ∀ w < n + r, suspendedValue C r fill x w = val C (List.ofFn x) w := by
  have hs := (suspendedValue_evalExcept C h r fill).2
  have ho := originalEvalExcept h r
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hv : w < n
    · exact (suspendedValue_raw C r fill x ⟨w, hv⟩).trans (ho.1 x ⟨w, hv⟩).symm
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < C.gates.length := by omega
      have he : j ≠ r := by omega
      have hOrig := ho.2 x j hj he
      dsimp only at hOrig
      rw [hs x j hj he, hOrig]
      congr 1
      apply List.map_congr_left
      intro w hw'
      have hwlt := h.2.1 j hj w hw'
      exact ih w hwlt (by omega)

/-- The shadow evaluation assigns values to deleted prefix gates. The
    concrete circuit retains only the specified prefix and adds precisely
    one binary gate per suffix gate, redirecting the hole to an earlier wire. -/
theorem replayJunkSuffix {n : ℕ} (C : Circuit) (hC : IsAO2 n C)
    (Keep : ℕ → Prop) {r : ℕ} (hr : r < C.gates.length)
    (D : Circuit) (hD : IsAO2 n D) {i : ℕ} (hi : i < n + D.gates.length)
    (ρ : ℕ → ℕ)
    (hprefix : ∀ w, RetainedWire n Keep r w → ρ w < n + D.gates.length ∧
      ∀ x : Fin n → Bool, val D (List.ofFn x) (ρ w) = val C (List.ofFn x) w)
    (hclosed : ∀ j, r < j → j < C.gates.length → ∀ w ∈ (gateAt C j).inputs,
      w < n + r → RetainedWire n Keep r w)
    (houtLow : n + r ≤ C.output) (houtHigh : C.output < n + C.gates.length) :
    ∃ (E : Circuit) (W : (Fin n → Bool) → ℕ → Bool),
      IsAO2 n E ∧ E.gates.length = D.gates.length + (C.gates.length - (r + 1)) ∧
      EvalExcept n C r W ∧
      (∀ x : Fin n → Bool, W x (n + r) = val D (List.ofFn x) i) ∧
      ∀ x : Fin n → Bool, E.eval (List.ofFn x) = W x C.output := by
  let P := fun j => r ≤ j ∨ Keep j
  let fill := fun x : Fin n → Bool => val D (List.ofFn x) i
  let V := suspendedValue C r fill
  let ρ' := fun w => if w = n + r then i else ρ w
  have hV : EvalExcept n C r V := suspendedValue_evalExcept C hC r fill
  have hh (x : Fin n → Bool) : V x (n + r) = fill x := suspendedValue_hole C r fill x
  have hbase (w : ℕ) (hw : RetainedWire n P (r + 1) w) :
      ρ' w < n + D.gates.length ∧
      ∀ x : Fin n → Bool, val D (List.ofFn x) (ρ' w) = V x w := by
    by_cases he : w = n + r
    · subst w
      exact ⟨by simpa [ρ'] using hi, fun x => by simpa [ρ', fill] using (hh x).symm⟩
    · have hh' : RetainedWire n Keep r w := by
        rcases hw with hw | ⟨j, hj, hp, rfl⟩
        · exact Or.inl hw
        · rcases hp with hp | hp
          · exact (he (by omega)).elim
          · exact Or.inr ⟨j, by omega, hp, rfl⟩
      have hw' : w < n + r := by
        rcases hh' with hw' | ⟨j, hj, _, rfl⟩
        · omega
        · omega
      have hb := hprefix w hh'
      rw [show ρ' w = ρ w from ite_eq_right he]
      exact ⟨hb.1, fun x => (hb.2 x).trans (suspendedValue_before C hC r hr fill x w hw').symm⟩
  have hcl (j : ℕ) (hs : r + 1 ≤ j) (hj : j < C.gates.length)
      (w : ℕ) (hw : w ∈ (gateAt C j).inputs) : RetainedWire n P j w := by
    have hlt := hC.2.1 j hj w hw
    by_cases he : w < n + r
    · rcases hclosed j (by omega) hj w hw he with hv | ⟨k, hk, hp, rfl⟩
      · exact Or.inl hv
      · exact Or.inr ⟨k, by omega, Or.inr hp, rfl⟩
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      exact Or.inr ⟨k, by omega, Or.inl (by omega), rfl⟩
  let k := C.gates.length - (r + 1)
  have hcount : r + 1 + k = C.gates.length := by dsimp [k]; omega
  obtain ⟨E, σ, hE, hlen, hσ⟩ := replaySuffix C hC P (r + 1) D hD V ρ'
    hbase hcl
    (fun x j hs hj => hV.2 x j hj (by omega)) k (by omega)
  have hout : RetainedWire n P (r + 1 + k) C.output := by
    obtain ⟨j, he⟩ : ∃ j, C.output = n + j := ⟨C.output - n, by omega⟩
    exact Or.inr ⟨j, by omega, Or.inl (by omega), he⟩
  let F : Circuit := ⟨E.gates, σ C.output⟩
  exact ⟨F, V, hE, hlen, hV, hh, fun x => (hσ _ hout).2 x⟩

#print axioms replayJunkSuffix

/-- No least lift-fixed circuit with a unique dirty AND can have two
    distinct raw vertices shared by the junk's operands. -/
theorem noTwoOverlap {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C) (h4 : NoFourCycle G)
    {r a b : ℕ} (hJ : junk G C = {r}) (hab : (gateAt C r).inputs = [a, b])
    {A B : Finset (Fin n)} (hA : RawForm C r a A false) (hB : RawForm C r b B false)
    {u v : Fin n} (huA : u ∈ A) (huB : u ∈ B) (hvA : v ∈ A) (hvB : v ∈ B)
    (hne : u ≠ v) : False := by
  classical
  obtain ⟨c, ⟨huc, hvc⟩, _⟩ := twoOverlapCommonCentre G C h hl h4 hJ hab hA hB huA huB hvA hvB hne
  by_cases exposed : c ∈ A ∨ c ∈ B
  · exact noExposedTwoOverlap G C h hl h4 hJ hab hA hB huA huB hvA hvB hne huc hvc exposed
  obtain ⟨hr, hand, _⟩ := junkMember G C hJ
  let keep := fun j => j < r ∧ AvoidJunk n C r (n + j)
  have closed (j : ℕ) (hj : j < C.gates.length) (hp : keep j)
      (w : ℕ) (hm : w ∈ (gateAt C j).inputs) : RetainedWire n keep j w := by
    have hw := h.1.2.1 j hj w hm
    by_cases hn : w < n
    · exact Or.inl hn
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < j := by omega
      exact Or.inr ⟨k, hk, ⟨hk.trans hp.1, .input hj hp.1.ne hm hp.2⟩, rfl⟩
  obtain ⟨D, ρ, hD, hlenD, hρ⟩ := compileSelection C h.1 keep closed r hr.le
  let needed := fun w => ¬ CleanWire G C w
  let V := fun (x : Fin n → Bool) w => val C (List.ofFn (neighbourhoodInput G c x)) w
  have raw (w : ℕ) (hw : w < n) (_ : needed w) : WireAvailable D (fun x => V x w) := by
    let z : Fin n := ⟨w, hw⟩
    have hz (x : Fin n → Bool) : V x w = neighbourhoodInput G c x z :=
      (originalEvalExcept h.1 r).1 (neighbourhoodInput G c x) z
    by_cases ha : G.Adj c z
    · refine Or.inr ⟨w, by omega, fun x => ?_⟩
      change val D (List.ofFn x) w = V x w
      rw [hz x, show neighbourhoodInput G c x z = x z by simp [neighbourhoodInput, ha]]
      exact (originalEvalExcept hD r).1 x z
    · refine Or.inl (fun x => ?_)
      change V x w = false
      rw [hz x]
      simp [neighbourhoodInput, ha]
  have retained (j : ℕ) (hj : j < r) (hp : keep j) (hd : needed (n + j)) :
      WireAvailable D (fun x => V x (n + j)) := by
    obtain ⟨S, hS⟩ := preJunkDirtyRaw G C h hl hJ (by omega : n + j < n + r) hd
    obtain ⟨d, hs⟩ := protectedPureSupportNeighbour G C h hl h4 hJ hab hA hB huA huB hvA hvB
      hne huc hvc hp.2 (by omega) hd hS
    obtain ⟨hi, he⟩ := hρ (n + j) (Or.inr ⟨j, hj, hp, rfl⟩)
    exact protectedFilteredAvailable G h4 h.1 hS hi he c d hs
  have skipped (j : ℕ) (hj : j < r) (hp : ¬ keep j) (_ : needed (n + j)) :
      (∀ w ∈ (gateAt C j).inputs, needed w) ∧
      ∀ x, V x (n + j) = true ↔ ∃ w ∈ (gateAt C j).inputs, V x w = true := by
    have hj' := hj.trans hr
    obtain ⟨hor, hd⟩ := unprotectedPreJunkDirtyOr G C h hl hJ hj (fun hav => hp ⟨hj, hav⟩)
    refine ⟨fun w hw hc => hd (cleanWireReader G C h hl hj' hw hc).2, fun x => ?_⟩
    exact evalExcept_or (originalEvalExcept h.1 r) hj' hj.ne hor (neighbourhoodInput G c x)
  obtain ⟨F, hF, hDF, hlenF, haveWire⟩ := compileAvailablePrefix C D h.1 hD r hr.le keep needed V raw retained skipped
  have hma : a ∈ (gateAt C r).inputs := by rw [hab]; simp
  have ha := h.1.2.1 r hr a hma
  have hdirty := noCleanAndOperand G C h r a hr hma hand
  have haMasked (x : Fin n → Bool) : V x a = true ↔ hits (A.filter (G.Adj c)) x :=
    (pureProviderValue h.1 hA _).trans (hitsNeighbourhoodInput G c x A)
  have hu : u ∈ A.filter (G.Adj c) := Finset.mem_filter.mpr ⟨huA, (G.adj_comm u c).mp huc⟩
  have hactive : V (fun _ => true) a = true := (haMasked _).mpr ⟨u, hu, rfl⟩
  have hsmall : F.gates.length ≤ r := by
    have hc := Finset.card_filter_add_card_filter_not (s := Finset.range r) keep
    rw [Finset.card_range] at hc
    omega
  obtain ⟨i, hi, hfillF⟩ : ∃ i < n + F.gates.length, ∀ x, val F (List.ofFn x) i = V x a := by
    rcases haveWire a ha hdirty with hzero | hx
    · have hf : V (fun _ => true) a = false := hzero _
      cases hf.symm.trans hactive
    · exact hx
  have hprefix (w : ℕ) (hw : RetainedWire n keep r w) : ρ w < n + F.gates.length ∧
      ∀ x : Fin n → Bool, val F (List.ofFn x) (ρ w) = val C (List.ofFn x) w := by
    obtain ⟨hbound, hvalue⟩ := hρ w hw
    refine ⟨by have := hDF.1; omega, fun x => (hDF.2 x _ hbound).trans (hvalue x)⟩
  have hclosed (j : ℕ) (hrj : r < j) (hj : j < C.gates.length)
      (w : ℕ) (hm : w ∈ (gateAt C j).inputs) (hw : w < n + r) : RetainedWire n keep r w := by
    by_cases hn : w < n
    · exact Or.inl hn
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < r := by omega
      exact Or.inr ⟨k, hk, ⟨hk, .input hj hrj.ne' hm (avoidJunkOfGe G C h hrj.le hj)⟩, rfl⟩
  have hout := outputLast G C h (by omega)
  obtain ⟨E, W, hE, hlenE, hW, hwFill, hwOut⟩ := replayJunkSuffix C h.1 keep hr F hF hi ρ
    hprefix hclosed (by omega) (by omega)
  apply noTwoOverlapWithRebuiltFilter G C h hl h4 hJ hab hA hB huA huB hvA hvB hne huc hvc
    (R := A) (Or.inl rfl) (fun ha => exposed (Or.inl ha)) E hE ?_ hW ?_ hwOut
  · change E.gates.length < C.gates.length
    omega
  · intro x
    rw [hwFill x, hfillF x]
    exact haMasked x

#print axioms noTwoOverlap

/-- A centre is exposed when it belongs to an opposite support of a clean
    AND whose other operand carries the junk. -/
def ExposedCentre {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (r : ℕ) (c : Fin n) : Prop :=
  ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧ BelowF G C j ∧
    ∃ S T, OrientedTop C r j S T true ∧ c ∈ T

theorem suspendedFalseSound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    {r : ℕ} (hJ : junk G C = {r}) {W : (Fin n → Bool) → ℕ → Bool}
    (hW : EvalExcept n C r W) (hzero : ∀ x, W x (n + r) = false) :
    ∀ x, W x C.output = true → graphFun G ∅ x = true := by
  intro x hx
  obtain ⟨j, hj, hop, hc, hw⟩ := (collectorSemantics G C h hl hJ hW x).mp hx
  obtain ⟨S, T, f, htop⟩ := orientedTop G C h hl hJ hj hop hc
  obtain ⟨hs, ht⟩ := (htop W hW x).mp hw
  have hraw : hits S x := by simpa [hzero x] using hs
  exact hc x ((htop _ (originalEvalExcept h.1 r) x).mpr ⟨Or.inl hraw, ht⟩)

/-- Suspending the junk at false is sound. Every lost edge belongs to one
    of the stars at the exposed centres, at most one for each support. -/
theorem lostEdgesInExposedStars {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C) (h4 : NoFourCycle G)
    {r a b : ℕ} (hJ : junk G C = {r}) (hab : (gateAt C r).inputs = [a, b])
    {A B : Finset (Fin n)} (hA : RawForm C r a A false) (hB : RawForm C r b B false)
    (hd : Disjoint A B) (ha : 1 < A.card) (hb : 1 < B.card) :
    ∃ EA EB : Finset (Fin n), EA ⊆ A ∧ EB ⊆ B ∧ EA.card ≤ 1 ∧ EB.card ≤ 1 ∧
      (∀ c ∈ EA, ∀ v ∈ B, G.Adj c v) ∧ (∀ c ∈ EB, ∀ v ∈ A, G.Adj c v) ∧
      ∀ W, EvalExcept n C r W → (∀ x, W x (n + r) = false) →
        (∀ x, W x C.output = true → graphFun G ∅ x = true) ∧
        ∀ u v, G.Adj u v → W (pairInput u v) C.output = true ∨
          (∃ c ∈ EA, ∃ w ∈ B, pairInput u v c = true ∧ pairInput u v w = true) ∨
          (∃ c ∈ EB, ∃ w ∈ A, pairInput u v c = true ∧ pairInput u v w = true) := by
  classical
  let EA := A.filter (ExposedCentre G C r)
  let EB := B.filter (ExposedCentre G C r)
  obtain ⟨hr, hand, _⟩ := junkMember G C hJ
  let V := fun (x : Fin n → Bool) w => val C (List.ofFn x) w
  have hV : EvalExcept n C r V := originalEvalExcept h.1 r
  have hprod := originalJunkProduct h.1 hr hand hab hA hB
  have starA (c : Fin n) (hc : c ∈ EA) (v : Fin n) (hv : v ∈ B) : G.Adj c v := by
    obtain ⟨hcA, j, _, _, hclean, S, T, htop, hcT⟩ := Finset.mem_filter.mp hc
    exact (carrierCross G h.1 hprod hclean htop hcA hv hcT
      (u := v) (v := c) (Or.inr rfl) (Or.inl rfl)).symm
  have starB (c : Fin n) (hc : c ∈ EB) (v : Fin n) (hv : v ∈ A) : G.Adj c v := by
    obtain ⟨hcB, j, _, _, hclean, S, T, htop, hcT⟩ := Finset.mem_filter.mp hc
    exact (carrierCross G h.1 hprod hclean htop hv hcB hcT
      (u := v) (v := c) (Or.inl rfl) (Or.inr rfl)).symm
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp ha
  obtain ⟨s, hs, t, ht, hst⟩ := Finset.one_lt_card.mp hb
  have smallA : EA.card ≤ 1 := Finset.card_le_one.mpr fun c hc d hc' =>
    (commonNeighborUnique G h4 hst (starA c hc s hs).symm (starA c hc t ht).symm
      (starA d hc' s hs).symm (starA d hc' t ht).symm).symm
  have smallB : EB.card ≤ 1 := Finset.card_le_one.mpr fun c hc d hc' =>
    (commonNeighborUnique G h4 hpq (starB c hc p hp).symm (starB c hc q hq).symm
      (starB d hc' p hp).symm (starB d hc' q hq).symm).symm
  refine ⟨EA, EB, Finset.filter_subset _ _, Finset.filter_subset _ _, smallA, smallB,
    starA, starB, ?_⟩
  intro W hW hzero
  refine ⟨suspendedFalseSound G C h hl hJ hW hzero, ?_⟩
  · intro u v huv
    let x := pairInput u v
    have hv : V x C.output = true := (congrFun h.2.1 x).trans (pair_true G u v huv)
    obtain ⟨j, hj, hop, hc, hvj⟩ := (collectorSemantics G C h hl hJ hV x).mp hv
    obtain ⟨S, T, f, htop⟩ := orientedTop G C h hl hJ hj hop hc
    obtain ⟨hs, ht⟩ := (htop V hV x).mp hvj
    rcases hs with hs | ⟨rfl, hjunk⟩
    · exact Or.inl ((collectorSemantics G C h hl hJ hW x).mpr
        ⟨j, hj, hop, hc, (htop W hW x).mpr ⟨Or.inl hs, ht⟩⟩)
    · obtain ⟨⟨p, hpA, hpx⟩, ⟨q, hqB, hqx⟩⟩ := (hprod x).mp hjunk
      obtain ⟨z, hzT, hzx⟩ := ht
      have hpq : p ≠ q := fun he => Finset.disjoint_left.mp hd hpA (he.symm ▸ hqB)
      have hp' : p = u ∨ p = v := by simpa [x, pairInput] using hpx
      have hq' : q = u ∨ q = v := by simpa [x, pairInput] using hqx
      have hz' : z = u ∨ z = v := by simpa [x, pairInput] using hzx
      have hz : z = p ∨ z = q := by aesop
      have hex : ExposedCentre G C r z := ⟨j, hj, hop, hc, S, T, htop, hzT⟩
      rcases hz with rfl | rfl
      · exact Or.inr (Or.inl ⟨z, Finset.mem_filter.mpr ⟨hpA, hex⟩, q, hqB, hzx, hqx⟩)
      · exact Or.inr (Or.inr ⟨z, Finset.mem_filter.mpr ⟨hqB, hex⟩, p, hpA, hzx, hpx⟩)

#print axioms suspendedFalseSound
#print axioms lostEdgesInExposedStars

private lemma exposedCentreAdjacencies {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {C : Circuit} (h : IsAO2 n C) {r : ℕ} {A B : Finset (Fin n)}
    (hp : ∀ x : Fin n → Bool, val C (List.ofFn x) (n + r) = true ↔ hits A x ∧ hits B x)
    {s c : Fin n} (hsA : s ∈ A) (hsB : s ∈ B) (hc : ExposedCentre G C r c) :
    G.Adj s c ∧ (c ∈ A → ∀ b ∈ B, G.Adj b c) ∧ (c ∈ B → ∀ a ∈ A, G.Adj a c) := by
  obtain ⟨j, _, _, hclean, S, T, htop, hcT⟩ := hc
  exact ⟨carrierCross G h hp hclean htop hsA hsB hcT (Or.inl rfl) (Or.inl rfl),
    fun hcA _ hb => carrierCross G h hp hclean htop hcA hb hcT (Or.inr rfl) (Or.inl rfl),
    fun hcB _ ha => carrierCross G h hp hclean htop ha hcB hcT (Or.inl rfl) (Or.inr rfl)⟩

/-- With a shared vertex and at least two vertices per operand, at most
    one vertex in either operand is exposed. Only the triangle and C4
    exclusions are needed for this geometry. -/
theorem uniqueExposedOverlapCentre {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (h4 : NoFourCycle G)
    (htri : ∀ {s c d : Fin n}, G.Adj s c → G.Adj s d → ¬ G.Adj c d)
    {r a b : ℕ} (hJ : junk G C = {r}) (hab : (gateAt C r).inputs = [a, b])
    {A B : Finset (Fin n)} (hA : RawForm C r a A false) (hB : RawForm C r b B false)
    {s u v : Fin n} (hsA : s ∈ A) (hsB : s ∈ B) (hu : u ∈ A) (hv : v ∈ B)
    (hus : u ≠ s) (hvs : v ≠ s)
    {c d : Fin n} (hc : ExposedCentre G C r c) (hd : ExposedCentre G C r d)
    (hcm : c ∈ A ∨ c ∈ B) (hdm : d ∈ A ∨ d ∈ B) : d = c := by
  obtain ⟨hr, hand, _⟩ := junkMember G C hJ
  have hp := originalJunkProduct h.1 hr hand hab hA hB
  obtain ⟨hsc, hcA, hcB⟩ := exposedCentreAdjacencies G h.1 hp hsA hsB hc
  obtain ⟨hsd, hdA, hdB⟩ := exposedCentreAdjacencies G h.1 hp hsA hsB hd
  rcases hcm with hca | hcb <;> rcases hdm with hda | hdb
  · exact commonNeighborUnique G h4 hvs (hcA hca v hv) hsc (hdA hda v hv) hsd
  · exact (htri hsc hsd (hdB hdb c hca)).elim
  · exact (htri hsc hsd (hdA hda c hcb)).elim
  · exact commonNeighborUnique G h4 hus (hcB hcb u hu) hsc (hdB hdb u hu) hsd

#print axioms uniqueExposedOverlapCentre

/-- A protected provider reaching a shared vertex contributes through a
    clean raw product. Those contributions survive any junk redirection. -/
theorem protectedSharedSupport {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    {r a b : ℕ} (hJ : junk G C = {r}) (hab : (gateAt C r).inputs = [a, b])
    {A B : Finset (Fin n)} (hA : RawForm C r a A false) (hB : RawForm C r b B false)
    {s : Fin n} (hsA : s ∈ A) (hsB : s ∈ B)
    {R : Finset (Fin n)} (hs : s ∈ R) {w : ℕ} (hp : AvoidJunk n C r w)
    (hforce : ∀ V, EvalExcept n C r V → ∀ x, hits R x → V x w = true) :
    ∃ d : Fin n, (∀ z ∈ R, G.Adj d z) ∧
      ∀ V, EvalExcept n C r V → ∀ x, hits R x → x d = true → V x C.output = true := by
  let U := fun (x : Fin n → Bool) k => val C (List.ofFn x) k
  have hU : EvalExcept n C r U := originalEvalExcept h.1 r
  obtain ⟨hr, hjunk, _⟩ := junkMember G C hJ
  have hprod := originalJunkProduct h.1 hr hjunk hab hA hB
  have htop : ∀ {j p q : ℕ} {Q : Finset (Fin n)} {g : Bool},
      j < C.gates.length → (gateAt C j).op = GateOp.and → BelowF G C j →
      ((gateAt C j).inputs = [p, q] ∨ (gateAt C j).inputs = [q, p]) →
      RawForm C r q Q g →
      (∀ V, EvalExcept n C r V → ∀ x, hits R x → V x p = true) →
      ∃ d : Fin n, (∀ z ∈ R, G.Adj d z) ∧
        ∀ V, EvalExcept n C r V → ∀ x, hits R x → x d = true → V x C.output = true := by
    intro j p q Q g hj hand hc hpq hQ hfp
    have hand' (V) (hV : EvalExcept n C r V) (x) (hp' : V x p = true)
        (hq' : V x q = true) : V x (n + j) = true := by
      have hnr := cleanDifferent G C hJ hc
      rcases hpq with he | he
      · exact (evalExcept_and hV hj hnr hand he x).mpr ⟨hp', hq'⟩
      · exact (evalExcept_and hV hj hnr hand he x).mpr ⟨hq', hp'⟩
    have hg : g = false := by
      cases g with
      | false => rfl
      | true =>
        let x := pairInput s s
        have hx : x s = true := by simp [x, pairInput]
        have hj : U x (n + r) = true := (hprod x).mpr ⟨⟨s, hsA, hx⟩, ⟨s, hsB, hx⟩⟩
        have hq := (hQ.2 U hU x).mpr (Or.inr ⟨rfl, hj⟩)
        have hp := hfp U hU x ⟨s, hs, hx⟩
        exact (G.ne_of_adj (adjOfPair G (hc x (hand' U hU x hp hq))) rfl).elim
    subst g
    have hq : q < n + j := by
      apply h.1.2.1 j hj q
      rcases hpq with he | he <;> simp [he]
    have hall : U (fun _ => true) q = true := allTrueWires h.1 q (by omega)
    have hsem (V) (hV : EvalExcept n C r V) (x) : V x q = true ↔ hits Q x := by
      simpa [hits] using hQ.2 V hV x
    obtain ⟨d, hd, _⟩ := (hsem U hU _).mp hall
    refine ⟨d, ?_, fun V hV x hx hdx => (collectorSemantics G C h hl hJ hV x).mpr
      ⟨j, hj, hand, hc, hand' V hV x (hfp V hV x hx) ((hsem V hV x).mpr ⟨d, hd, hdx⟩)⟩⟩
    intro z hz
    let x := pairInput d z
    have hdx : x d = true := by simp [x, pairInput]
    have hzx : x z = true := by simp [x, pairInput]
    exact adjOfPair G (hc x (hand' U hU x (hfp U hU x ⟨z, hz, hzx⟩)
      ((hsem U hU x).mpr ⟨d, hd, hdx⟩)))
  induction hp with
  | output =>
    let x := pairInput s s
    have hx : x s = true := by simp [x, pairInput]
    have ho : U x C.output = true := hforce U hU x ⟨s, hs, hx⟩
    have he : U x C.output = graphFun G ∅ x := congrFun h.2.1 x
    exact (G.ne_of_adj (adjOfPair G (he.symm.trans ho)) rfl).elim
  | @input j w hj hjr hmem _ ih =>
    rcases h.1.1 _ (gateAt_mem hj) with hand | hor
    · have hc : BelowF G C j := by
        by_contra hd
        exact hjr (uniqueDirtyAnd G C hJ hj hd hand)
      obtain ⟨p, q, P, Q, f, g, he, hP, hQ, _⟩ := topProduct G C h hl hJ hj hand hc
      have hw : w = p ∨ w = q := by simpa [he] using hmem
      rcases hw with rfl | rfl
      · exact htop hj hand hc (Or.inl he) hQ hforce
      · exact htop hj hand hc (Or.inr he) hP hforce
    · exact ih (fun V hV x hx => (evalExcept_or hV hj hjr hor x).mpr ⟨w, hmem, hforce V hV x hx⟩)

/-- A provider containing the shared vertex and an adjacent vertex cannot
    have an output path avoiding the junk. -/
theorem adjacentSharedProviderExclusive {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    (htri : ∀ {s c d : Fin n}, G.Adj s c → G.Adj s d → ¬ G.Adj c d)
    {r a b : ℕ} (hJ : junk G C = {r}) (hab : (gateAt C r).inputs = [a, b])
    {A B : Finset (Fin n)} (hA : RawForm C r a A false) (hB : RawForm C r b B false)
    {s c : Fin n} (hsA : s ∈ A) (hsB : s ∈ B) (hadj : G.Adj s c)
    {R : Finset (Fin n)} (hs : s ∈ R) (hc : c ∈ R) {w : ℕ}
    (hR : RawForm C r w R false) : ¬ AvoidJunk n C r w := by
  intro hp
  obtain ⟨d, hd, _⟩ := protectedSharedSupport G C h hl hJ hab hA hB hsA hsB hs hp
    (fun V hV x hx => (hR.2 V hV x).mpr (Or.inl hx))
  exact htri (hd s hs) (hd c hc) hadj

/-- A protected provider with at least two vertices already covers its
    star when its support lies in the exposed centre's neighbourhood. -/
theorem protectedSharedStarSurvives {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C) (h4 : NoFourCycle G)
    {r a b : ℕ} (hJ : junk G C = {r}) (hab : (gateAt C r).inputs = [a, b])
    {A B : Finset (Fin n)} (hA : RawForm C r a A false) (hB : RawForm C r b B false)
    {s c : Fin n} (hsA : s ∈ A) (hsB : s ∈ B)
    {R : Finset (Fin n)} (hs : s ∈ R) {t : Fin n} (ht : t ∈ R) (hts : t ≠ s)
    (hadj : ∀ z ∈ R, G.Adj z c) {w : ℕ} (hp : AvoidJunk n C r w)
    (hR : RawForm C r w R false) :
    ∀ V, EvalExcept n C r V → ∀ x, hits R x → x c = true → V x C.output = true := by
  obtain ⟨d, hd, hout⟩ := protectedSharedSupport G C h hl hJ hab hA hB hsA hsB hs hp
    (fun V hV x hx => (hR.2 V hV x).mpr (Or.inl hx))
  have he := commonNeighborUnique G h4 hts (hadj t ht) (hadj s hs)
    ((G.adj_comm d t).mp (hd t ht)) ((G.adj_comm d s).mp (hd s hs))
  simpa [he] using hout

#print axioms protectedSharedSupport
#print axioms adjacentSharedProviderExclusive
#print axioms protectedSharedStarSurvives

/-- Redirecting the junk to the shared input is sound. Any edge lost by
    this redirection belongs to the exposed star, away from the shared input. -/
theorem exposedSingletonRedirect {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    {r a b : ℕ} (hJ : junk G C = {r}) (hab : (gateAt C r).inputs = [a, b])
    {A B : Finset (Fin n)} (hA : RawForm C r a A false) (hB : RawForm C r b B false)
    {s c : Fin n} (hsA : s ∈ A) (hsB : s ∈ B) (hcB : c ∉ B)
    (hshared : ∀ z ∈ A, z ∈ B → z = s)
    (honly : ∀ z, ExposedCentre G C r z → z ∈ A ∨ z ∈ B → z = c)
    {W : (Fin n → Bool) → ℕ → Bool} (hW : EvalExcept n C r W)
    (hfill : ∀ x, W x (n + r) = x s) :
    (∀ x, W x C.output = true → graphFun G ∅ x = true) ∧
      ∀ u v, G.Adj u v → W (pairInput u v) C.output = true ∨
        ∃ z ∈ B, z ≠ s ∧ pairInput u v c = true ∧ pairInput u v z = true := by
  let V := fun (x : Fin n → Bool) w => val C (List.ofFn x) w
  have hV : EvalExcept n C r V := originalEvalExcept h.1 r
  obtain ⟨hr, hand, _⟩ := junkMember G C hJ
  have hprod := originalJunkProduct h.1 hr hand hab hA hB
  constructor
  · intro x hx
    obtain ⟨j, hj, hop, hc, hv⟩ := (collectorSemantics G C h hl hJ hW x).mp hx
    obtain ⟨S, T, f, ht⟩ := orientedTop G C h hl hJ hj hop hc
    obtain ⟨hp, hq⟩ := (ht W hW x).mp hv
    apply hc x ((ht V hV x).mpr ⟨?_, hq⟩)
    rcases hp with hp | ⟨hf, hw⟩
    · exact Or.inl hp
    · have hsx : x s = true := (hfill x).symm.trans hw
      exact Or.inr ⟨hf, (hprod x).mpr ⟨⟨s, hsA, hsx⟩, ⟨s, hsB, hsx⟩⟩⟩
  · intro u v huv
    let x := pairInput u v
    have hv : V x C.output = true := (congrFun h.2.1 x).trans (pair_true G u v huv)
    obtain ⟨j, hj, hop, hc, hvj⟩ := (collectorSemantics G C h hl hJ hV x).mp hv
    obtain ⟨S, T, f, ht⟩ := orientedTop G C h hl hJ hj hop hc
    obtain ⟨hp, hq⟩ := (ht V hV x).mp hvj
    have keep (hk : hits S x ∨ (f = true ∧ W x (n + r) = true)) : W x C.output = true :=
      (collectorSemantics G C h hl hJ hW x).mpr ⟨j, hj, hop, hc, (ht W hW x).mpr ⟨hk, hq⟩⟩
    by_cases hraw : hits S x
    · exact Or.inl (keep (Or.inl hraw))
    · have ⟨hf, hvold⟩ := hp.resolve_left hraw
      by_cases hsx : x s = true
      · exact Or.inl (keep (Or.inr ⟨hf, (hfill x).trans hsx⟩))
      subst f
      obtain ⟨⟨p, hpA, hpx⟩, ⟨q, hqB, hqx⟩⟩ := (hprod x).mp hvold
      obtain ⟨z, hzT, hzx⟩ := hq
      have hpq : p ≠ q := by
        intro he
        have hps := hshared p hpA (he.symm ▸ hqB)
        exact hsx (hps ▸ hpx)
      have hp' : p = u ∨ p = v := by simpa [x, pairInput] using hpx
      have hq' : q = u ∨ q = v := by simpa [x, pairInput] using hqx
      have hz' : z = u ∨ z = v := by simpa [x, pairInput] using hzx
      have hz : z = p ∨ z = q := by aesop
      have hex : ExposedCentre G C r z := ⟨j, hj, hop, hc, S, T, ht, hzT⟩
      rcases hz with hz | hz
      · have hc' := honly z hex (Or.inl (hz.symm ▸ hpA))
        exact Or.inr ⟨q, hqB, fun he => hsx (he ▸ hqx), hc' ▸ hzx, hqx⟩
      · have hzB : z ∈ B := hz.symm ▸ hqB
        have hc' := honly z hex (Or.inr hzB)
        exact (hcB (hc' ▸ hzB)).elim

#print axioms exposedSingletonRedirect

/-- An exposed singleton-overlap case with a protected opposite provider
    admits strict deletion by redirecting to the shared input. -/
theorem noExposedSingletonProtectedProvider {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C) (h4 : NoFourCycle G)
    (htri : ∀ {s c d : Fin n}, G.Adj s c → G.Adj s d → ¬ G.Adj c d)
    {r a b : ℕ} (hJ : junk G C = {r}) (hab : (gateAt C r).inputs = [a, b])
    {A B : Finset (Fin n)} (hA : RawForm C r a A false) (hB : RawForm C r b B false)
    {s c t : Fin n} (hsA : s ∈ A) (hsB : s ∈ B) (hcA : c ∈ A) (htB : t ∈ B) (hts : t ≠ s)
    (hshared : ∀ z ∈ A, z ∈ B → z = s) (hex : ExposedCentre G C r c)
    (hprotected : AvoidJunk n C r b) : False := by
  obtain ⟨hr, hand, _⟩ := junkMember G C hJ
  have ⟨hsc, hadj, _⟩ := exposedCentreAdjacencies G h.1
    (originalJunkProduct h.1 hr hand hab hA hB) hsA hsB hex
  have hcs := (G.ne_of_adj hsc).symm
  have hcB : c ∉ B := fun hcB => hcs (hshared c hcA hcB)
  have honly (z : Fin n) (hz : ExposedCentre G C r z) (hzm : z ∈ A ∨ z ∈ B) :=
    uniqueExposedOverlapCentre G C h h4 htri hJ hab hA hB hsA hsB hcA htB hcs hts hex hz (Or.inl hcA) hzm
  have hi : s.val < n + r := by omega
  let D := bypass n C r s.val
  let W : (Fin n → Bool) → ℕ → Bool := fun x w =>
    val D (List.ofFn x) (aliasWire (n + r) s.val w)
  have hW : EvalExcept n C r W := bypassEvalExcept h.1 hr hi
  have hfill (x : Fin n → Bool) : W x (n + r) = x s := by
    dsimp [W, D]
    rw [aliasWire_self, bypass_val_lt (n := n) (by simp) hr s.val hi]
    exact (originalEvalExcept h.1 r).1 x s
  have hout (x : Fin n → Bool) : D.eval (List.ofFn x) = W x C.output := rfl
  have hD : IsAO2 n D := by
    change IsAO2 n (bypass n C r s.val)
    rw [← erase_eq_bypass n C r s.val hr]
    exact erase_exactAO h.1 hr hi
  obtain ⟨hsafe, hedge⟩ := exposedSingletonRedirect G C h hl hJ hab hA hB hsA hsB hcB hshared honly hW hfill
  have hstar := protectedSharedStarSurvives G C h hl h4 hJ hab hA hB hsA hsB hsB htB hts
    (hadj hcA) hprotected hB W hW
  have hcorrect : circuitFun n D = graphFun G ∅ := by
    funext x
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hx
      exact hsafe x ((hout x).symm.trans hx)
    · intro hx
      obtain ⟨u, v, huv, hu, hv⟩ := (graph_true G x).mp hx
      apply circuit_monotone n D (ao_mono hD) (pairInput u v) x ?_ ?_
      · intro w hw
        have hw' : w = u ∨ w = v := by simpa [pairInput] using hw
        rcases hw' with rfl | rfl
        · exact hu
        · exact hv
      · rw [hout]
        rcases hedge u v huv with h | ⟨z, hz, _, hcx, hzx⟩
        · exact h
        · exact hstar _ ⟨z, hz, hzx⟩ hcx
  have hmin := h.2.2 D hD hcorrect
  have hsize : D.size = C.gates.length - 1 := bypass_length n C r s.val
  change C.gates.length ≤ D.size at hmin
  omega

#print axioms noExposedSingletonProtectedProvider


/-- In the prefix of a unique-junk circuit, an unprotected provider active
    on a singleton has an unprotected OR ancestor (possibly itself) with
    an active operand that is raw or protected. -/
theorem firstUnprotectedSingletonOr {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    {r : ℕ} (hJ : junk G C = {r}) (s : Fin n) :
    ∀ j < r, ¬ AvoidJunk n C r (n + j) → val C (List.ofFn (pairInput s s)) (n + j) = true →
      ∃ k ≤ j, (k = j ∨ InCone n C k j) ∧ ¬ AvoidJunk n C r (n + k) ∧
        (gateAt C k).op = GateOp.or ∧ ∃ w ∈ (gateAt C k).inputs,
          val C (List.ofFn (pairInput s s)) w = true ∧ (w = s.val ∨ AvoidJunk n C r w) := by
  have hr := (junkMember G C hJ).1
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj hjp hjv
    have hjlen := hj.trans hr
    have hor := (unprotectedPreJunkDirtyOr G C h hl hJ hj hjp).1
    obtain ⟨w, hw, hwlt, hwv⟩ := (val_or (n := n) (by simp) hjlen hor).mp hjv
    by_cases hwraw : w < n
    · let v : Fin n := ⟨w, hwraw⟩
      have hv : pairInput s s v = true :=
        ((originalEvalExcept h.1 r).1 (pairInput s s) v).symm.trans hwv
      have he : v = s := by simpa [pairInput] using hv
      exact ⟨j, le_rfl, Or.inl rfl, hjp, hor, w, hw, hwv, Or.inl (congrArg Fin.val he)⟩
    by_cases hwp : AvoidJunk n C r w
    · exact ⟨j, le_rfl, Or.inl rfl, hjp, hor, w, hw, hwv, Or.inr hwp⟩
    obtain ⟨i, rfl⟩ : ∃ i, w = n + i := ⟨w - n, by omega⟩
    have hij : i < j := by omega
    have hcone : InCone n C i j := (coneRec hjlen i).mpr
      ⟨n + i, hw, by omega, hwlt, Or.inl (by omega)⟩
    obtain ⟨k, hk, hc, hkp, hko, w, hw, hv, hp⟩ := ih i hij (hij.trans hj) hwp hwv
    have hkj : InCone n C k j := by
      rcases hc with rfl | hki
      · exact hcone
      · exact coneTrans _ hjlen _ _ hki hcone
    exact ⟨k, hk.trans hij.le, Or.inr hkj, hkp, hko, w, hw, hv, hp⟩

#print axioms firstUnprotectedSingletonOr

/-- A strict provider trim has enough room for a clean AND star and one
    OR to join it with the redirected circuit. -/
theorem noExposedSingletonWithTrimmedStar {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    {r a b : ℕ} (hJ : junk G C = {r}) (hab : (gateAt C r).inputs = [a, b])
    {A B : Finset (Fin n)} (hA : RawForm C r a A false) (hB : RawForm C r b B false)
    {s c : Fin n} (hsA : s ∈ A) (hsB : s ∈ B) (hcB : c ∉ B)
    (hshared : ∀ z ∈ A, z ∈ B → z = s)
    (honly : ∀ z, ExposedCentre G C r z → z ∈ A ∨ z ∈ B → z = c)
    (hadj : ∀ z ∈ B, G.Adj c z)
    {W : (Fin n → Bool) → ℕ → Bool} (hW : EvalExcept n C r W)
    (hfill : ∀ x, W x (n + r) = x s)
    (D : Circuit) (hD : IsAO2 n D) (hlen : D.gates.length + 2 < C.gates.length)
    (hout : D.output < n + D.gates.length)
    (hval : ∀ x, D.eval (List.ofFn x) = W x C.output)
    {i : ℕ} (hi : i < n + D.gates.length) {R : Finset (Fin n)} (hR : R ⊆ B)
    (htrim : ∀ x, val D (List.ofFn x) i = true ↔ hits R x)
    (hcover : ∀ x z, z ∈ B → z ≠ s → x c = true → x z = true →
      z ∈ R ∨ W x C.output = true) : False := by
  obtain ⟨hsafe, hedge⟩ := exposedSingletonRedirect G C h hl hJ hab hA hB hsA hsB hcB hshared honly hW hfill
  let F := appendBinary D GateOp.and c.val i
  have hc : c.val < n + D.gates.length := by omega
  obtain ⟨hFlen, hF, hkeep, hnew⟩ := appendBinary_spec hD (Or.inl rfl) hc hi
  change F.gates.length = D.gates.length + 1 at hFlen
  have hFo : D.output < n + F.gates.length := by omega
  obtain ⟨E, hE, hElen, _, heval, _⟩ := compileCollector F hF D.output hFo [n + D.gates.length]
    (by intro j hj; simp at hj; omega)
  have heval' (x : Fin n → Bool) : E.eval (List.ofFn x) = true ↔
      W x C.output = true ∨ (x c = true ∧ hits R x) := by
    have hold : val D (List.ofFn x) D.output = W x C.output := hval x
    have hraw : val D (List.ofFn x) c.val = x c := (originalEvalExcept hD r).1 x c
    rw [heval x, hkeep x D.output hout, hold]
    simp only [List.mem_singleton, exists_eq_left]
    rw [hnew x, hraw]
    simp [GateOp.eval, htrim x]
  have hcorrect : circuitFun n E = graphFun G ∅ := by
    funext x
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hx
      rcases (heval' x).mp hx with hv | ⟨hcx, z, hz, hzx⟩
      · exact hsafe x hv
      · exact (graph_true G x).mpr ⟨c, z, hadj z (hR hz), hcx, hzx⟩
    · intro hx
      obtain ⟨u, v, huv, hu, hv⟩ := (graph_true G x).mp hx
      apply circuit_monotone n E (ao_mono hE) (pairInput u v) x ?_ ?_
      · intro w hw
        have hw' : w = u ∨ w = v := by simpa [pairInput] using hw
        rcases hw' with rfl | rfl
        · exact hu
        · exact hv
      · apply (heval' _).mpr
        rcases hedge u v huv with hw | ⟨z, hz, hzs, hcx, hzx⟩
        · exact Or.inl hw
        · rcases hcover _ z hz hzs hcx hzx with hzR | hw
          · exact Or.inr ⟨hcx, z, hzR, hzx⟩
          · exact Or.inl hw
  have hmin := h.2.2 E hE hcorrect
  change C.gates.length ≤ E.gates.length at hmin
  simp only [List.length_singleton] at hElen
  omega

#print axioms noExposedSingletonWithTrimmedStar


end ResearchVerification.OneJunkErase
