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

/-- A value is identically false or is represented by an existing wire. -/
def WireAvailable {n : ℕ} (D : Circuit) (f : (Fin n → Bool) → Bool) : Prop :=
  (∀ x, f x = false) ∨ ∃ w < n + D.gates.length, ∀ x, val D (List.ofFn x) w = f x

private def PreservesWires (n : ℕ) (D E : Circuit) : Prop :=
  D.gates.length ≤ E.gates.length ∧
    ∀ (x : Fin n → Bool) w, w < n + D.gates.length → val E (List.ofFn x) w = val D (List.ofFn x) w

private lemma wireAvailablePreserved {n : ℕ} {D E : Circuit} (h : PreservesWires n D E)
    {f : (Fin n → Bool) → Bool} (hf : WireAvailable D f) : WireAvailable E f := by
  rcases hf with hz | ⟨w, hw, he⟩
  · exact Or.inl hz
  · exact Or.inr ⟨w, by have := h.1; omega, fun x => (h.2 x w hw).trans (he x)⟩

private lemma wireAvailableFalseOfTop {n : ℕ} {D : Circuit} (hD : IsAO2 n D)
    {f : (Fin n → Bool) → Bool} (hf : WireAvailable D f) (hzero : f (fun _ => true) = false) :
    ∀ x, f x = false := by
  rcases hf with hfalse | ⟨w, hw, he⟩
  · exact hfalse
  · have ht := (he _).symm.trans (allTrueWires hD w hw)
    rw [hzero] at ht
    cases ht

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

private def maskedValue {n : ℕ} (C : Circuit) (r : ℕ)
    (mask : ℕ → ℕ → Bool) (fill : (Fin n → Bool) → Bool) (x : Fin n → Bool) (w : ℕ) : Bool :=
  if hw : w < n then x ⟨w, hw⟩
  else if w = n + r then fill x
  else (gateAt C (w - n)).op.eval ((gateAt C (w - n)).inputs.attach.map fun v =>
    if mask (w - n) v.val then false
    else if _hv : v.val < w then maskedValue C r mask fill x v.val else false)
termination_by w

private abbrev suspendedValue {n : ℕ} (C : Circuit) (r : ℕ)
    (fill : (Fin n → Bool) → Bool) := maskedValue C r (fun _ _ => false) fill

private lemma maskedValue_raw {n : ℕ} (C : Circuit) (r : ℕ) (mask : ℕ → ℕ → Bool)
    (fill : (Fin n → Bool) → Bool) (x : Fin n → Bool) (v : Fin n) :
    maskedValue C r mask fill x v.val = x v := by
  rw [maskedValue, dite_eq_left v.isLt]

private lemma maskedValue_hole {n : ℕ} (C : Circuit) (r : ℕ) (mask : ℕ → ℕ → Bool)
    (fill : (Fin n → Bool) → Bool) (x : Fin n → Bool) :
    maskedValue C r mask fill x (n + r) = fill x := by
  rw [maskedValue, dite_eq_right (by omega), ite_eq_left rfl]

private lemma maskedValue_gate {n : ℕ} (C : Circuit) (h : IsAO2 n C) (r : ℕ)
    (mask : ℕ → ℕ → Bool) (fill : (Fin n → Bool) → Bool) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) (hne : j ≠ r) :
    maskedValue C r mask fill x (n + j) = (gateAt C j).op.eval
      ((gateAt C j).inputs.map fun v => if mask j v then false else maskedValue C r mask fill x v) := by
  rw [maskedValue, dite_eq_right (by omega), ite_eq_right (by omega), Nat.add_sub_cancel_left]
  congr 1
  conv => rhs; rw [← List.attach_map_val]
  apply List.map_congr_left
  intro v _
  rw [dite_eq_left (h.2.1 j hj v.val v.property)]

private lemma suspendedValue_raw {n : ℕ} (C : Circuit) (r : ℕ)
    (fill : (Fin n → Bool) → Bool) (x : Fin n → Bool) (v : Fin n) :
    suspendedValue C r fill x v.val = x v := by
  exact maskedValue_raw C r _ fill x v

private lemma suspendedValue_hole {n : ℕ} (C : Circuit) (r : ℕ)
    (fill : (Fin n → Bool) → Bool) (x : Fin n → Bool) :
    suspendedValue C r fill x (n + r) = fill x := by
  exact maskedValue_hole C r _ fill x

private lemma suspendedValue_evalExcept {n : ℕ} (C : Circuit) (h : IsAO2 n C) (r : ℕ)
    (fill : (Fin n → Bool) → Bool) : EvalExcept n C r (suspendedValue C r fill) := by
  refine ⟨suspendedValue_raw C r fill, ?_⟩
  intro x j hj hne
  simpa using maskedValue_gate C h r (fun _ _ => false) fill x hj hne

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

/-- A path through OR gates to a clean AND whose other operand survives
    suspension on the all-true input. -/
inductive ResidualUse {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (r : ℕ) (live : ℕ → Bool) : ℕ → Prop where
  | top {j w p : ℕ} (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and)
      (hc : BelowF G C j)
      (hwp : (gateAt C j).inputs = [w, p] ∨ (gateAt C j).inputs = [p, w])
      (hp : live p = true) : ResidualUse G C r live w
  | throughOr {j w : ℕ} (hj : j < C.gates.length) (hjr : j ≠ r)
      (hor : (gateAt C j).op = GateOp.or) (hw : w ∈ (gateAt C j).inputs)
      (hjuse : ResidualUse G C r live (n + j)) : ResidualUse G C r live w

private theorem residualUseDirty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    {r : ℕ} {live : ℕ → Bool} {w : ℕ} (hw : ResidualUse G C r live w) :
    ¬ CleanWire G C w := by
  induction hw with
  | @top j w p hj hand hc hwp hp =>
    have hm : w ∈ (gateAt C j).inputs := by
      rcases hwp with he | he <;> simp [he]
    exact noCleanAndOperand G C h j w hj hm hand
  | @throughOr j w hj hjr hor hm _ ih =>
    exact fun hc => ih ((cleanWireGate G C j).mpr (cleanWireReader G C h hl hj hm hc).2)

/-- A replay that keeps the clean gate equations and all residual OR
    dependencies retains every input accepted by the suspended output. -/
theorem residualOutputPreserved {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    {r : ℕ} (hJ : junk G C = {r}) {W Z : (Fin n → Bool) → ℕ → Bool}
    (hW : EvalExcept n C r W) (hzero : ∀ x, W x (n + r) = false)
    (hZraw : ∀ x (v : Fin n), Z x v.val = x v)
    (hZzero : ∀ x, Z x (n + r) = false)
    (hZgate : ∀ x j, j < C.gates.length → j ≠ r →
      BelowF G C j ∨ ResidualUse G C r (W (fun _ => true)) (n + j) →
      Z x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (Z x))) :
    ∀ x, W x C.output = true → Z x C.output = true := by
  intro x hx
  have main : ∀ j < C.gates.length,
      (ResidualUse G C r (W (fun _ => true)) (n + j) → Z x (n + j) = W x (n + j)) ∧
      (BelowF G C j → W x (n + j) = true → Z x (n + j) = true) := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      have earlier (w : ℕ) (hw : w < n + j)
          (hwuse : ResidualUse G C r (W (fun _ => true)) w) : Z x w = W x w := by
        by_cases hraw : w < n
        · let v : Fin n := ⟨w, hraw⟩
          exact (hZraw x v).trans (hW.1 x v).symm
        · obtain ⟨i, rfl⟩ : ∃ i, w = n + i := ⟨w - n, by omega⟩
          exact (ih i (by omega) (by omega)).1 hwuse
      constructor
      · intro huse
        by_cases hjr : j = r
        · subst j
          exact (hZzero x).trans (hzero x).symm
        have hd := residualUseDirty G C h hl huse
        have hor : (gateAt C j).op = GateOp.or := by
          rcases h.1.1 _ (gateAt_mem hj) with hand | hor
          · exact (hjr (uniqueDirtyAnd G C hJ hj
              (fun hc => hd ((cleanWireGate G C j).mpr hc)) hand)).elim
          · exact hor
        rw [hZgate x j hj hjr (Or.inr huse), hW.2 x j hj hjr]
        congr 1
        apply List.map_congr_left
        intro w hw
        exact earlier w (h.1.2.1 j hj w hw) (.throughOr hj hjr hor hw huse)
      · intro hc hv
        have hjr := cleanDifferent G C hJ hc
        rcases h.1.1 _ (gateAt_mem hj) with hand | hor
        · obtain ⟨a, b, A, B, f, g, hab, hA, hB, _⟩ := topProduct G C h hl hJ hj hand hc
          obtain ⟨ha, hb⟩ := (evalExcept_and hW hj hjr hand hab x).mp hv
          have atTop {w : ℕ} {S : Finset (Fin n)} {t : Bool}
              (hS : RawForm C r w S t) (hw : W x w = true) :
              W (fun _ => true) w = true := by
            obtain ⟨v, hmem, _⟩ := ((hS.2 W hW x).mp hw).resolve_right (by simp [hzero x])
            exact (hS.2 W hW _).mpr (Or.inl ⟨v, hmem, rfl⟩)
          have hal := h.1.2.1 j hj a (by simp [hab])
          have hbl := h.1.2.1 j hj b (by simp [hab])
          have hza := (earlier a hal (.top hj hand hc (Or.inl hab) (atTop hB hb))).trans ha
          have hzb := (earlier b hbl (.top hj hand hc (Or.inr hab) (atTop hA ha))).trans hb
          rw [hZgate x j hj hjr (Or.inl hc), hand, hab]
          simp [GateOp.eval, hza, hzb]
        · obtain ⟨w, hm, hw⟩ := (evalExcept_or hW hj hjr hor x).mp hv
          have hcw := cleanOrOperands G C h.1 hj hor hc hm
          have hlt := h.1.2.1 j hj w hm
          by_cases hraw : w < n
          · exact (rawNotClean G C ⟨w, hraw⟩ hcw).elim
          · obtain ⟨i, rfl⟩ : ∃ i, w = n + i := ⟨w - n, by omega⟩
            have hwz := (ih i (by omega) (by omega)).2 hcw hw
            rw [hZgate x j hj hjr (Or.inl hc), hor]
            simpa [GateOp.eval, List.any_map, List.any_eq_true] using
              (show ∃ w ∈ (gateAt C j).inputs, Z x w = true from ⟨n + i, hm, hwz⟩)
  have hr := (junkMember G C hJ).1
  have hlast := outputLast G C h (by omega : 0 < C.gates.length)
  rw [hlast] at hx ⊢
  have hclean : BelowF G C (C.gates.length - 1) := by
    intro y hy
    have he : C.eval (List.ofFn y) = graphFun G ∅ y := congrFun h.2.1 y
    rw [← he]
    change val C (List.ofFn y) C.output = true
    rwa [hlast]
  exact (main (C.gates.length - 1) (by omega)).2 hclean hx

#print axioms residualOutputPreserved

/-- Every raw contribution carried by a residual use contributes its
    whole star at some vertex to the suspended output. -/
theorem residualUseCoversSupport {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    {r : ℕ} (hJ : junk G C = {r}) {W : (Fin n → Bool) → ℕ → Bool}
    (hW : EvalExcept n C r W) (hzero : ∀ x, W x (n + r) = false)
    {w : ℕ} (hw : ResidualUse G C r (W (fun _ => true)) w)
    {R : Finset (Fin n)} (hforce : ∀ x, (∃ z ∈ R, x z = true) → W x w = true) :
    ∃ d : Fin n, ∀ z ∈ R, G.Adj z d ∧ W (pairInput z d) C.output = true := by
  induction hw with
  | @top j w p hj hand hc hwp hp =>
    have hm : p ∈ (gateAt C j).inputs := by
      rcases hwp with he | he <;> simp [he]
    have hlt := h.1.2.1 j hj p hm
    obtain ⟨P, b, hP⟩ := dirtyRawForm G C h hl hJ p (by omega)
      (noCleanAndOperand G C h j p hj hm hand)
    have hraw (x) : W x p = true ↔ ∃ d ∈ P, x d = true := by
      simpa [hzero x] using hP.2 W hW x
    obtain ⟨d, hd, _⟩ := (hraw _).mp hp
    refine ⟨d, fun z hz => ?_⟩
    let x := pairInput z d
    have hwx : W x w = true := hforce x ⟨z, hz, by simp [x, pairInput]⟩
    have hpx : W x p = true := (hraw x).mpr ⟨d, hd, by simp [x, pairInput]⟩
    have hnr := cleanDifferent G C hJ hc
    have hv : W x (n + j) = true := by
      rcases hwp with he | he
      · exact (evalExcept_and hW hj hnr hand he x).mpr ⟨hwx, hpx⟩
      · exact (evalExcept_and hW hj hnr hand he x).mpr ⟨hpx, hwx⟩
    have hout := (collectorSemantics G C h hl hJ hW x).mpr ⟨j, hj, hand, hc, hv⟩
    exact ⟨adjOfPair G (suspendedFalseSound G C h hl hJ hW hzero x hout), hout⟩
  | @throughOr j w hj hjr hor hm _ ih =>
    exact ih (fun x hx => (evalExcept_or hW hj hjr hor x).mpr ⟨w, hm, hforce x hx⟩)

/-- A protected pure provider with at least two vertices can only serve
    the unique common neighbour of those vertices. -/
theorem residualUseCoversPureStar {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C) (h4 : NoFourCycle G)
    {r : ℕ} (hJ : junk G C = {r}) {W : (Fin n → Bool) → ℕ → Bool}
    (hW : EvalExcept n C r W) (hzero : ∀ x, W x (n + r) = false)
    {w : ℕ} {R : Finset (Fin n)} (hR : RawForm C r w R false)
    (hcard : 1 < R.card) {d : Fin n} (hstar : ∀ z ∈ R, G.Adj z d)
    (hw : ResidualUse G C r (W (fun _ => true)) w) :
    ∀ z ∈ R, W (pairInput z d) C.output = true := by
  obtain ⟨e, he⟩ := residualUseCoversSupport G C h hl hJ hW hzero hw
    (fun x hx => (hR.2 W hW x).mpr (Or.inl hx))
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp hcard
  have hed := commonNeighborUnique G h4 hpq (hstar p hp) (hstar q hq)
    (he p hp).1 (he q hq).1
  subst e
  exact fun z hz => (he z hz).2

#print axioms residualUseCoversSupport
#print axioms residualUseCoversPureStar

/-- Trace a distinguished input through an exclusive provider to the
    first OR where it arrives from a raw input or a protected wire. -/
theorem firstUnprotectedResidualOr {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    {r : ℕ} (hJ : junk G C = {r}) {W : (Fin n → Bool) → ℕ → Bool}
    (hW : EvalExcept n C r W) (s : Fin n) :
    ∀ j < r, ¬ CleanWire G C (n + j) →
      ¬ ResidualUse G C r (W (fun _ => true)) (n + j) →
      W (pairInput s s) (n + j) = true →
      ∃ k ≤ j, (k = j ∨ InCone n C k j) ∧
        ¬ ResidualUse G C r (W (fun _ => true)) (n + k) ∧
        ¬ CleanWire G C (n + k) ∧
        (gateAt C k).op = GateOp.or ∧ ∃ w ∈ (gateAt C k).inputs,
          ¬ CleanWire G C w ∧ W (pairInput s s) w = true ∧
          (w = s.val ∨ ResidualUse G C r (W (fun _ => true)) w) ∧
          ∀ x, W x w = true → W x (n + j) = true := by
  have hr := (junkMember G C hJ).1
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj hd hjuse hjv
    have hjlen := hj.trans hr
    have hor : (gateAt C j).op = GateOp.or := by
      rcases h.1.1 _ (gateAt_mem hjlen) with hand | hor
      · exact (hj.ne (uniqueDirtyAnd G C hJ hjlen
          (fun hc => hd ((cleanWireGate G C j).mpr hc)) hand)).elim
      · exact hor
    obtain ⟨w, hw, hwv⟩ := (evalExcept_or hW hjlen hj.ne hor (pairInput s s)).mp hjv
    have hwlt := h.1.2.1 j hjlen w hw
    have hwd : ¬ CleanWire G C w := fun hc =>
      hd ((cleanWireGate G C j).mpr (cleanWireReader G C h hl hjlen hw hc).2)
    have hprop (x) (hx : W x w = true) : W x (n + j) = true :=
      (evalExcept_or hW hjlen hj.ne hor x).mpr ⟨w, hw, hx⟩
    by_cases hwraw : w < n
    · let v : Fin n := ⟨w, hwraw⟩
      have hv : pairInput s s v = true := (hW.1 (pairInput s s) v).symm.trans hwv
      have he : v = s := by simpa [pairInput] using hv
      exact ⟨j, le_rfl, Or.inl rfl, hjuse, hd, hor, w, hw, hwd, hwv,
        Or.inl (congrArg Fin.val he), hprop⟩
    by_cases hwuse : ResidualUse G C r (W (fun _ => true)) w
    · exact ⟨j, le_rfl, Or.inl rfl, hjuse, hd, hor, w, hw, hwd, hwv, Or.inr hwuse, hprop⟩
    obtain ⟨i, rfl⟩ : ∃ i, w = n + i := ⟨w - n, by omega⟩
    have hij : i < j := by omega
    have hcone : InCone n C i j := (coneRec hjlen i).mpr
      ⟨n + i, hw, by omega, hwlt, Or.inl (by omega)⟩
    obtain ⟨k, hk, hc, hkp, hkd, hko, v, hv, hvd, hvv, hpu, hreach⟩ :=
      ih i hij (hij.trans hj) hwd hwuse hwv
    have hkj : InCone n C k j := by
      rcases hc with rfl | hki
      · exact hcone
      · exact coneTrans _ hjlen _ _ hki hcone
    exact ⟨k, hk.trans hij.le, Or.inr hkj, hkp, hkd, hko, v, hv, hvd, hvv, hpu,
      fun x hx => hprop x (hreach x hx)⟩

#print axioms firstUnprotectedResidualOr

/-- A counted gate realizing a pure disjunction needs at least two
    vertices in its support, by nonzero evaluation and minimality. -/
private theorem pureGateSupportCard {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) {r j : ℕ} (hj : j < C.gates.length)
    {R : Finset (Fin n)} (hR : RawForm C r (n + j) R false) : 1 < R.card := by
  let V := fun (x : Fin n → Bool) w => val C (List.ofFn x) w
  have hV : EvalExcept n C r V := originalEvalExcept h.1 r
  have hraw (x) : V x (n + j) = true ↔ ∃ z ∈ R, x z = true := by
    simpa using hR.2 V hV x
  obtain ⟨s, hs, _⟩ := (hraw _).mp (allTrueWires h.1 (n + j) (by omega))
  by_contra! hcard
  apply noEqualEarlier G C h j s.val hj (by have := s.isLt; omega)
  intro x
  change V x (n + j) = V x s.val
  rw [hV.1 x s]
  apply Bool.eq_iff_iff.mpr
  rw [hraw x]
  constructor
  · rintro ⟨z, hz, hzx⟩
    exact (Finset.card_le_one.mp hcard z hz s hs) ▸ hzx
  · exact fun hx => ⟨s, hs, hx⟩

/-- If some edge of a provider's star is missing after suspension,
    tracing the distinguished vertex yields an exclusive OR. Its
    incoming edge can be suppressed in a trimmed copy: the source is
    the distinguished input itself or a protected substar already
    covered by the residual output. -/
theorem residualStarTrimBoundary {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C) (h4 : NoFourCycle G)
    {r j : ℕ} (hJ : junk G C = {r}) (hj : j < r)
    (hdirty : ¬ CleanWire G C (n + j))
    {R : Finset (Fin n)} (hR : RawForm C r (n + j) R false)
    {d s z : Fin n} (hstar : ∀ u ∈ R, G.Adj u d) (hs : s ∈ R) (hz : z ∈ R)
    {W : (Fin n → Bool) → ℕ → Bool} (hW : EvalExcept n C r W)
    (hzero : ∀ x, W x (n + r) = false) (hlost : W (pairInput z d) C.output = false) :
    ∃ k ≤ j, (k = j ∨ InCone n C k j) ∧
      ¬ ResidualUse G C r (W (fun _ => true)) (n + k) ∧
      ¬ CleanWire G C (n + k) ∧
      (gateAt C k).op = GateOp.or ∧ ∃ w ∈ (gateAt C k).inputs,
        W (pairInput s s) w = true ∧
        (w = s.val ∨ ∃ Q : Finset (Fin n), RawForm C r w Q false ∧ s ∈ Q ∧ Q ⊆ R ∧
          ResidualUse G C r (W (fun _ => true)) w ∧
          ∀ u ∈ Q, W (pairInput u d) C.output = true) := by
  have hr := (junkMember G C hJ).1
  have hjlen := hj.trans hr
  have hjuse : ¬ ResidualUse G C r (W (fun _ => true)) (n + j) := by
    intro hp
    exact Bool.noConfusion (hlost.symm.trans (residualUseCoversPureStar G C h hl h4 hJ
      hW hzero hR (pureGateSupportCard G C h hjlen hR) hstar hp z hz))
  have hjs : W (pairInput s s) (n + j) = true :=
    (hR.2 W hW _).mpr (Or.inl ⟨s, hs, by simp [pairInput]⟩)
  obtain ⟨k, hk, hc, hkp, hkd, hko, w, hw, hwd, hwv, hboundary, hreach⟩ :=
    firstUnprotectedResidualOr G C h hl hJ hW s j hj hdirty hjuse hjs
  refine ⟨k, hk, hc, hkp, hkd, hko, w, hw, hwv, ?_⟩
  by_cases hraw : w < n
  · let v : Fin n := ⟨w, hraw⟩
    have hv : pairInput s s v = true := (hW.1 (pairInput s s) v).symm.trans hwv
    have he : v = s := by simpa [pairInput] using hv
    exact Or.inl (congrArg Fin.val he)
  have hwp := hboundary.resolve_left (by have := s.isLt; omega)
  have hwlt := h.1.2.1 k (hk.trans_lt hjlen) w hw
  obtain ⟨Q, hQ⟩ := preJunkDirtyRaw G C h hl hJ (by omega : w < n + r) hwd
  have hqs : s ∈ Q := by
    obtain ⟨v, hv, hs⟩ := ((hQ.2 W hW _).mp hwv).resolve_right (by simp)
    have he : v = s := by simpa [pairInput] using hs
    exact he ▸ hv
  have hsub : Q ⊆ R := by
    intro u hu
    have ht := hreach (pairInput u u) ((hQ.2 W hW _).mpr
      (Or.inl ⟨u, hu, by simp [pairInput]⟩))
    obtain ⟨v, hv, hu⟩ := ((hR.2 W hW _).mp ht).resolve_right (by simp)
    have he : v = u := by simpa [pairInput] using hu
    exact he ▸ hv
  obtain ⟨i, rfl⟩ : ∃ i, w = n + i := ⟨w - n, by omega⟩
  exact Or.inr ⟨Q, hQ, hqs, hsub, hwp, residualUseCoversPureStar G C h hl h4 hJ hW hzero
    hQ (pureGateSupportCard G C h (by omega) hQ) (fun u hu => hstar u (hsub hu)) hwp⟩

#print axioms residualStarTrimBoundary

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

/-- An AND with a false operand is represented by false without adding a gate. -/
private lemma appendAvailableAnd {n : ℕ} (D : Circuit) (hD : IsAO2 n D)
    {f g : (Fin n → Bool) → Bool} (hf : WireAvailable D f) (hg : WireAvailable D g) :
    ∃ E, IsAO2 n E ∧ PreservesWires n D E ∧ E.gates.length ≤ D.gates.length + 1 ∧
      ((∀ x, f x = false) ∨ (∀ x, g x = false) → E.gates.length ≤ D.gates.length) ∧
      WireAvailable E (fun x => f x && g x) := by
  have hself : PreservesWires n D D := ⟨le_rfl, fun _ _ _ => rfl⟩
  rcases hf with hf | ⟨a, ha, hfa⟩
  · exact ⟨D, hD, hself, by omega, fun _ => le_rfl, Or.inl (fun x => by simp [hf x])⟩
  · rcases hg with hg | ⟨b, hb, hgb⟩
    · exact ⟨D, hD, hself, by omega, fun _ => le_rfl, Or.inl (fun x => by simp [hg x])⟩
    · obtain ⟨hlen, hE, hkeep, hval⟩ := appendBinary_spec hD (Or.inl rfl) ha hb
      refine ⟨appendBinary D GateOp.and a b, hE, ⟨by omega, hkeep⟩, by omega, ?_, Or.inr ?_⟩
      · rintro (hf | hg)
        · have ht : f (fun _ => true) = true := (hfa _).symm.trans (allTrueWires hD a ha)
          cases (hf _).symm.trans ht
        · have ht : g (fun _ => true) = true := (hgb _).symm.trans (allTrueWires hD b hb)
          cases (hg _).symm.trans ht
      · refine ⟨n + D.gates.length, by omega, fun x => ?_⟩
        rw [hval x, hfa x, hgb x]
        simp [GateOp.eval]

private theorem compileMaskedSuspension {n : ℕ} (C : Circuit) (h : IsAO2 n C) {r : ℕ}
    (mask : ℕ → ℕ → Bool) (W : (Fin n → Bool) → ℕ → Bool)
    (hraw : ∀ x (v : Fin n), W x v.val = x v)
    (hgate : ∀ x j, j < C.gates.length → j ≠ r → W x (n + j) =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun v => if mask j v then false else W x v))
    (hzero : ∀ x, W x (n + r) = false)
    (dropped : Finset ℕ) (hd : dropped ⊆ Finset.range C.gates.length)
    (hdrop : ∀ j ∈ dropped, j = r ∨
      ∃ w ∈ (gateAt C j).inputs, mask j w = true ∨ W (fun _ => true) w = false) :
    ∃ D : Circuit, IsAO2 n D ∧ D.gates.length + dropped.card ≤ C.gates.length ∧
      ∀ w < n + C.gates.length, WireAvailable D (fun x => W x w) := by
  classical
  let budget := fun k => ((Finset.range k).filter fun j => j ∉ dropped).card
  have main : ∀ k ≤ C.gates.length, ∃ D : Circuit, IsAO2 n D ∧
      D.gates.length ≤ budget k ∧ ∀ w < n + k, WireAvailable D (fun x => W x w) := by
    intro k
    induction k with
    | zero =>
      intro _
      let D : Circuit := ⟨[], 0⟩
      have hD : IsAO2 n D := by
        refine ⟨fun g hg => ?_, fun j hj => ?_, fun g hg => ?_⟩ <;> simp [D] at *
      refine ⟨D, hD, by simp [D], fun w hw => Or.inr ⟨w, by simpa [D] using hw, ?_⟩⟩
      intro x
      let v : Fin n := ⟨w, by omega⟩
      exact ((originalEvalExcept hD r).1 x v).trans (hraw x v).symm
    | succ k ih =>
      intro hk
      obtain ⟨D, hD, hsize, havail⟩ := ih (by omega)
      have hj : k < C.gates.length := by omega
      have hcount : budget (k + 1) = budget k + if k ∈ dropped then 0 else 1 := by
        by_cases hm : k ∈ dropped
        · simp [budget, Finset.range_add_one, Finset.filter_insert, hm]
        · simp [budget, Finset.range_add_one, Finset.filter_insert, hm]
      have finish (E : Circuit) (hE : IsAO2 n E) (hkeep : PreservesWires n D E)
          (hbound : E.gates.length ≤ D.gates.length + 1)
          (hfree : k ∈ dropped → E.gates.length ≤ D.gates.length)
          (hw : WireAvailable E (fun x => W x (n + k))) :
          ∃ F : Circuit, IsAO2 n F ∧ F.gates.length ≤ budget (k + 1) ∧
            ∀ w < n + (k + 1), WireAvailable F (fun x => W x w) := by
        refine ⟨E, hE, ?_, fun w hwlt => ?_⟩
        · by_cases hm : k ∈ dropped
          · have := hfree hm
            simp only [hm, ite_true, Nat.add_zero] at hcount
            omega
          · simp only [hm, ite_false] at hcount
            omega
        · by_cases he : w = n + k
          · simpa [he] using hw
          · exact wireAvailablePreserved hkeep (havail w (by omega))
      by_cases he : k = r
      · exact finish D hD ⟨le_rfl, fun _ _ _ => rfl⟩ (by omega) (fun _ => le_rfl)
          (Or.inl (by simpa [he] using hzero))
      obtain ⟨p, q, hpq⟩ := twoOperands h hj
      have hp : p ∈ (gateAt C k).inputs := by simp [hpq]
      have hq : q ∈ (gateAt C k).inputs := by simp [hpq]
      let operand := fun w x => if mask k w then false else W x w
      have available (w) (hm : w ∈ (gateAt C k).inputs) : WireAvailable D (operand w) := by
        cases he : mask k w
        · simpa [operand, he] using havail w (h.2.1 k hj w hm)
        · exact Or.inl (by simp [operand, he])
      have hP := available p hp
      have hQ := available q hq
      have uncharged (hm : k ∈ dropped) :
          (∀ x, operand p x = false) ∨ (∀ x, operand q x = false) := by
        rcases (hdrop k hm).resolve_left he with ⟨w, hw, hz⟩
        have hz' : operand w (fun _ => true) = false := by
          rcases hz with hm | hv <;> simp [operand, *]
        have heq : w = p ∨ w = q := by simpa [hpq] using hw
        rcases heq with rfl | rfl
        · exact Or.inl (wireAvailableFalseOfTop hD hP hz')
        · exact Or.inr (wireAvailableFalseOfTop hD hQ hz')
      rcases h.1 _ (gateAt_mem hj) with hand | hor
      · obtain ⟨E, hE, hkeep, hbound, hfree, hw⟩ := appendAvailableAnd D hD hP hQ
        have hv : (fun x => operand p x && operand q x) = fun x => W x (n + k) := by
          funext x
          simpa [operand, hand, hpq, GateOp.eval] using (hgate x k hj he).symm
        exact finish E hE hkeep hbound (fun hm => hfree (uncharged hm)) (hv ▸ hw)
      · obtain ⟨E, hE, hkeep, hbound, hfree, hw⟩ := appendAvailableOr D hD hP hQ
        have hv : (fun x => operand p x || operand q x) = fun x => W x (n + k) := by
          funext x
          simpa [operand, hor, hpq, GateOp.eval] using (hgate x k hj he).symm
        exact finish E hE hkeep hbound (fun hm => hfree (uncharged hm)) (hv ▸ hw)
  obtain ⟨D, hD, hsize, hw⟩ := main C.gates.length le_rfl
  have hcard := Finset.card_sdiff_of_subset hd
  have he : budget C.gates.length = (Finset.range C.gates.length \ dropped).card := by
    unfold budget
    rw [Finset.sdiff_eq_filter]
  rw [he, hcard, Finset.card_range] at hsize
  have hdcard := Finset.card_le_card hd
  rw [Finset.card_range] at hdcard
  exact ⟨D, hD, by omega, hw⟩

/-- Compile the suspension without adding constants. Every charged index is
    the suspended gate or has a false operand at the all-true input. -/
theorem compileFalseSuspension {n : ℕ} (C : Circuit) (h : IsAO2 n C) {r : ℕ}
    {W : (Fin n → Bool) → ℕ → Bool} (hW : EvalExcept n C r W)
    (hzero : ∀ x, W x (n + r) = false)
    (dropped : Finset ℕ) (hd : dropped ⊆ Finset.range C.gates.length)
    (hdrop : ∀ j ∈ dropped, j = r ∨
      ∃ w ∈ (gateAt C j).inputs, W (fun _ => true) w = false) :
    ∃ D : Circuit, IsAO2 n D ∧ D.gates.length + dropped.card ≤ C.gates.length ∧
      ∀ w < n + C.gates.length, WireAvailable D (fun x => W x w) := by
  refine compileMaskedSuspension C h (fun _ _ => false) W hW.1 ?_ hzero dropped hd ?_
  · simpa using hW.2
  · simpa using hdrop

#print axioms compileFalseSuspension

private def trimOperand (k p : ℕ) : ℕ → ℕ → Bool :=
  fun j w => decide (j = k ∧ w = p)

private abbrev trimValue {n : ℕ} (C : Circuit) (r k p : ℕ) :=
  maskedValue (n := n) C r (trimOperand k p) (fun _ => false)

private theorem trimValueCompare {n : ℕ} (C : Circuit) (h : IsAO2 n C) {r : ℕ}
    {W : (Fin n → Bool) → ℕ → Bool} (hW : EvalExcept n C r W)
    (hzero : ∀ x, W x (n + r) = false) (k p : ℕ) (x : Fin n → Bool) :
    ∀ w < n + C.gates.length,
      (trimValue C r k p x w = true → W x w = true) ∧
      (W x p = false → trimValue C r k p x w = W x w) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hraw : w < n
    · let v : Fin n := ⟨w, hraw⟩
      have he : trimValue C r k p x w = W x w :=
        (maskedValue_raw C r _ _ x v).trans (hW.1 x v).symm
      exact ⟨fun ht => he ▸ ht, fun _ => he⟩
    obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    by_cases he : j = r
    · subst j
      have heq : trimValue C r k p x (n + r) = W x (n + r) :=
        (maskedValue_hole C r _ _ x).trans (hzero x).symm
      exact ⟨fun ht => heq ▸ ht, fun _ => heq⟩
    have hj : j < C.gates.length := by omega
    let input := fun v => if trimOperand k p j v then false else trimValue C r k p x v
    have hval : trimValue C r k p x (n + j) =
        (gateAt C j).op.eval ((gateAt C j).inputs.map input) :=
      maskedValue_gate C h r _ _ x hj he
    have hprev (v) (hv : v ∈ (gateAt C j).inputs) :=
      ih v (h.2.1 j hj v hv) (by have := h.2.1 j hj v hv; omega)
    have hle (v) (hv : v ∈ (gateAt C j).inputs) : input v = true → W x v = true := by
      cases hm : trimOperand k p j v
      · exact fun ht => (hprev v hv).1 (by simpa [input, hm] using ht)
      · simp [input, hm]
    constructor
    · rw [hval, hW.2 x j hj he]
      rcases h.1 _ (gateAt_mem hj) with hand | hor
      · simp only [hand, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply]
        exact fun ht v hv => hle v hv (ht v hv)
      · simp only [hor, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply]
        rintro ⟨v, hv, ht⟩
        exact ⟨v, hv, hle v hv ht⟩
    · intro hp
      rw [hval, hW.2 x j hj he]
      congr 1
      apply List.map_congr_left
      intro v hv
      by_cases hm : j = k ∧ v = p
      · have heq : trimOperand k p j v = true := decide_eq_true hm
        change (if trimOperand k p j v then false else trimValue C r k p x v) = W x v
        rw [ite_eq_left heq, hm.2, hp]
      · have heq : trimOperand k p j v ≠ true :=
          fun htrue => hm (of_decide_eq_true htrue)
        change (if trimOperand k p j v then false else trimValue C r k p x v) = W x v
        rw [ite_eq_right heq, (hprev v hv).2 hp]

private theorem trimValuePreservesOtherProvider {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    {r : ℕ} (hJ : junk G C = {r}) {W : (Fin n → Bool) → ℕ → Bool}
    (hW : EvalExcept n C r W) {k p : ℕ} (s : Fin n)
    (hk : W (pairInput s s) (n + k) = true) (x : Fin n → Bool) :
    ∀ w < n + r, ¬ CleanWire G C w → W (pairInput s s) w = false →
      trimValue C r k p x w = W x w := by
  have hr := (junkMember G C hJ).1
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hd hfalse
    by_cases hraw : w < n
    · let v : Fin n := ⟨w, hraw⟩
      exact (maskedValue_raw C r _ _ x v).trans (hW.1 x v).symm
    obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    have hj : j < C.gates.length := by omega
    have hjr : j ≠ r := by omega
    have hjk : j ≠ k := by
      rintro rfl
      exact Bool.noConfusion (hfalse.symm.trans hk)
    have hor : (gateAt C j).op = GateOp.or := by
      rcases h.1.1 _ (gateAt_mem hj) with hand | ho
      · exact (hjr (uniqueDirtyAnd G C hJ hj hd hand)).elim
      · exact ho
    change maskedValue C r (trimOperand k p) (fun _ => false) x (n + j) = W x (n + j)
    rw [maskedValue_gate C h.1 r _ _ x hj hjr, hW.2 x j hj hjr]
    congr 1
    apply List.map_congr_left
    intro v hv
    have hlt := h.1.2.1 j hj v hv
    have hvd : ¬ CleanWire G C v := fun hc =>
      hd (cleanWireReader G C h hl hj hv hc).2
    have hvfalse : W (pairInput s s) v = false := by
      cases he : W (pairInput s s) v
      · rfl
      · exact (Bool.noConfusion (hfalse.symm.trans
          ((evalExcept_or hW hj hjr hor (pairInput s s)).mpr ⟨v, hv, he⟩)))
    simpa [trimOperand, hjk] using ih v hlt (hlt.trans hw) hvd hvfalse

private theorem pairInputComm {n : ℕ} (u v : Fin n) : pairInput u v = pairInput v u := by
  funext z
  simp [pairInput, or_comm]

/-- With three direct junk readers, one exclusive provider OR pays for
    the second star even when the suspended output survives. -/
theorem noOneJunkWithTrimmedTwoStarsBudget {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    (h4 : NoFourCycle G) {r a b : ℕ} (hJ : junk G C = {r})
    (hab : (gateAt C r).inputs = [a, b])
    {A B : Finset (Fin n)} (hA : RawForm C r a A false)
    (hB : RawForm C r b B false) (hdisj : Disjoint A B) (hcardA : 1 < A.card)
    {s d : Fin n} (hs : s ∈ A) (hd : d ∈ B)
    (hstarA : ∀ v ∈ B, G.Adj s v) (hstarB : ∀ u ∈ A, G.Adj u d)
    {W : (Fin n → Bool) → ℕ → Bool} (hW : EvalExcept n C r W)
    (hzero : ∀ x, W x (n + r) = false)
    (hlost : ∃ z ∈ A, W (pairInput z d) C.output = false)
    (hcover : ∀ u v, G.Adj u v → W (pairInput u v) C.output = true ∨
      (pairInput u v s = true ∧ hits B (pairInput u v)) ∨
      (pairInput u v d = true ∧ hits A (pairInput u v)))
    (charges : Finset ℕ) (hcount : 2 ≤ charges.card)
    (hbudget : 3 ≤ charges.card ∨ W (fun _ => true) C.output = false)
    (hcharge : ∀ i ∈ charges, r < i ∧ i < C.gates.length ∧
      ∃ w ∈ (gateAt C i).inputs, W (fun _ => true) w = false) : False := by
  classical
  obtain ⟨hr, hand, _⟩ := junkMember G C hJ
  have ham : a ∈ (gateAt C r).inputs := by simp [hab]
  have hbm : b ∈ (gateAt C r).inputs := by simp [hab]
  have hal := h.1.2.1 r hr a ham
  have hbl := h.1.2.1 r hr b hbm
  have had := noCleanAndOperand G C h r a hr ham hand
  have hbd := noCleanAndOperand G C h r b hr hbm hand
  have hsemA (x) : W x a = true ↔ hits A x := by simpa [hits] using hA.2 W hW x
  have hsemB (x) : W x b = true ↔ hits B x := by simpa [hits] using hB.2 W hW x
  have hna : n ≤ a := by
    by_contra! hraw
    let u : Fin n := ⟨a, hraw⟩
    obtain ⟨v, hv, w, hw, hne⟩ := Finset.one_lt_card.mp hcardA
    have ident (z) (hz : z ∈ A) : u = z := by
      have ht := (hsemA (pairInput z z)).mpr ⟨z, hz, by simp [pairInput]⟩
      simpa [pairInput] using (hW.1 (pairInput z z) u).symm.trans ht
    exact hne ((ident v hv).symm.trans (ident w hw))
  obtain ⟨j, rfl⟩ : ∃ j, a = n + j := ⟨a - n, by omega⟩
  obtain ⟨z, hz, hmissing⟩ := hlost
  obtain ⟨k, hk, _, hku, hkd, hko, p, hp, hpactive, hpform⟩ :=
    residualStarTrimBoundary G C h hl h4 hJ (by omega) had hA hstarB hs hz hW hzero hmissing
  have hkr : k < r := by omega
  have hkl := hkr.trans hr
  have hks := (evalExcept_or hW hkl hkr.ne hko (pairInput s s)).mpr ⟨p, hp, hpactive⟩
  let Z := trimValue (n := n) C r k p
  have hZraw := maskedValue_raw C r (trimOperand k p) (fun _ : Fin n → Bool => false)
  have hZzero := maskedValue_hole C r (trimOperand k p) (fun _ : Fin n → Bool => false)
  have hZgate (x) (i) (hi : i < C.gates.length) (hir : i ≠ r) :=
    maskedValue_gate C h.1 r (trimOperand k p) (fun _ : Fin n → Bool => false) x hi hir
  have hkeep : ∀ x, W x C.output = true → Z x C.output = true := by
    apply residualOutputPreserved G C h hl hJ hW hzero hZraw hZzero
    intro x i hi hir hu
    have hik : i ≠ k := by
      rintro rfl
      exact hu.elim hkd hku
    simpa [trimOperand, hik] using hZgate x i hi hir
  have hbs : W (pairInput s s) b = false := by
    cases he : W (pairInput s s) b
    · rfl
    · obtain ⟨v, hv, hvx⟩ := (hsemB _).mp he
      have heq : v = s := by simpa [pairInput] using hvx
      exact (Finset.disjoint_left.mp hdisj hs (heq ▸ hv)).elim
  have hZB (x) : Z x b = W x b :=
    trimValuePreservesOtherProvider G C h hl hJ hW s hks x b hbl hbd hbs
  have outBound : C.output < n + C.gates.length := by
    have := outputLast G C h (by omega : 0 < C.gates.length)
    omega
  have habound : n + j < n + C.gates.length := by omega
  have hbbound : b < n + C.gates.length := by omega
  let f (x : Fin n → Bool) := (Z x C.output || (x s && Z x b)) || (x d && Z x (n + j))
  have hpositive (u v : Fin n) (huv : G.Adj u v) : f (pairInput u v) = true := by
    let x := pairInput u v
    have leftStar (hc : x s = true) (hb : hits B x) : f x = true := by
      simp [f, hc, hZB x, (hsemB x).mpr hb]
    have base (ho : W x C.output = true) : f x = true := by
      simp [f, hkeep x ho]
    rcases hcover u v huv with ho | ⟨hcs, hb⟩ | ⟨hcd, ha⟩
    · exact base ho
    · exact leftStar hcs hb
    obtain ⟨t, ht, htx⟩ := ha
    have htd := G.ne_of_adj (hstarB t ht)
    have hpair : x = pairInput t d := by
      have htuv : t = u ∨ t = v := by simpa [x, pairInput] using htx
      have hduv : d = u ∨ d = v := by simpa [x, pairInput] using hcd
      rcases htuv with ht' | ht' <;> rcases hduv with hd' | hd'
      · exact (htd (ht'.trans hd'.symm)).elim
      · simp [x, ht', hd']
      · simpa [x, ht', hd'] using pairInputComm u v
      · exact (htd (ht'.trans hd'.symm)).elim
    cases hpv : W x p
    · have he := (trimValueCompare C h.1 hW hzero k p x (n + j) habound).2 hpv
      have haz : Z x (n + j) = true := he.trans ((hsemA x).mpr ⟨t, ht, htx⟩)
      change ((Z x C.output || (x s && Z x b)) || (x d && Z x (n + j))) = true
      have hxd : x d = true := hcd
      rw [hxd, haz]
      simp
    · rcases hpform with rfl | ⟨Q, hQ, _, hQA, _, hQcover⟩
      · have hsx : x s = true := (hW.1 x s).symm.trans hpv
        exact leftStar hsx ⟨d, hd, hcd⟩
      · obtain ⟨q, hq, hqx⟩ := ((hQ.2 W hW x).mp hpv).resolve_right (by simp)
        have hqtd : q = t ∨ q = d := by simpa [hpair, pairInput] using hqx
        have hqd : q ≠ d := G.ne_of_adj (hstarB q (hQA hq))
        have hqt := hqtd.resolve_right hqd
        exact base (by rw [hpair, ← hqt]; exact hQcover q hq)
  have hsound (x) (hx : f x = true) : graphFun G ∅ x = true := by
    simp only [f, Bool.or_eq_true, Bool.and_eq_true] at hx
    rcases hx with (ho | ⟨hx, hb⟩) | ⟨hx, ha⟩
    · exact suspendedFalseSound G C h hl hJ hW hzero x
        ((trimValueCompare C h.1 hW hzero k p x C.output outBound).1 ho)
    · obtain ⟨v, hv, hvx⟩ := (hsemB x).mp ((hZB x).symm.trans hb)
      exact (graph_true G x).mpr ⟨s, v, hstarA v hv, hx, hvx⟩
    · obtain ⟨u, hu, hux⟩ := (hsemA x).mp
        ((trimValueCompare C h.1 hW hzero k p x (n + j) habound).1 ha)
      exact (graph_true G x).mpr ⟨u, d, hstarB u hu, hux, hx⟩
  have hrnot : r ∉ charges := fun hm => (Nat.lt_irrefl r) (hcharge r hm).1
  have hknot : k ∉ insert r charges := by
    intro hm
    rcases Finset.mem_insert.mp hm with he | hm
    · omega
    · have := (hcharge k hm).1
      omega
  let dropped := insert k (insert r charges)
  have hsize : dropped.card = charges.card + 2 := by
    rw [show dropped = insert k (insert r charges) from rfl,
      Finset.card_insert_of_notMem hknot, Finset.card_insert_of_notMem hrnot]
  obtain ⟨D, hD, hlen, hwires⟩ := compileMaskedSuspension C h.1 (trimOperand k p)
    Z hZraw hZgate hZzero dropped (by
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact Finset.mem_range.mpr hkl
      · rcases Finset.mem_insert.mp hi with rfl | hi
        · exact Finset.mem_range.mpr hr
        · exact Finset.mem_range.mpr (hcharge i hi).2.1) (by
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact Or.inr ⟨p, hp, Or.inl (by simp [trimOperand])⟩
      · rcases Finset.mem_insert.mp hi with rfl | hi
        · exact Or.inl rfl
        · obtain ⟨w, hw, hz⟩ := (hcharge i hi).2.2
          have hwb : w < n + C.gates.length :=
            (h.1.2.1 i (hcharge i hi).2.1 w hw).trans
              (Nat.add_lt_add_left (hcharge i hi).2.1 n)
          have hz' : Z (fun _ => true) w = false := by
            cases he : Z (fun _ => true) w
            · rfl
            · have ht := (trimValueCompare C h.1 hW hzero k p (fun _ => true) w hwb).1 he
              rw [hz] at ht
              contradiction
          exact Or.inr ⟨w, hw, Or.inr hz'⟩)
  have rawAvailable (F : Circuit) (hF : IsAO2 n F) (v : Fin n) :
      WireAvailable F (fun x => x v) :=
    Or.inr ⟨v, by have := v.isLt; omega, fun x => (originalEvalExcept hF r).1 x v⟩
  obtain ⟨D₁, hD₁, h₁, hlen₁, _, hs₁⟩ :=
    appendAvailableAnd D hD (rawAvailable D hD s) (hwires b hbbound)
  obtain ⟨D₂, hD₂, h₂, hlen₂, hfree₂, hs₂⟩ :=
    appendAvailableOr D₁ hD₁ (wireAvailablePreserved h₁ (hwires C.output outBound)) hs₁
  obtain ⟨D₃, hD₃, h₃, hlen₃, _, hs₃⟩ := appendAvailableAnd D₂ hD₂ (rawAvailable D₂ hD₂ d)
    (wireAvailablePreserved h₂ (wireAvailablePreserved h₁ (hwires (n + j) habound)))
  obtain ⟨D₄, hD₄, _, hlen₄, _, hf⟩ :=
    appendAvailableOr D₃ hD₃ (wireAvailablePreserved h₃ hs₂) hs₃
  change WireAvailable D₄ f at hf
  rcases hf with hf | ⟨o, _, hfo⟩
  · exact Bool.noConfusion ((hf _).symm.trans (hpositive s d (hstarA d hd)))
  · let E : Circuit := ⟨D₄.gates, o⟩
    have hE : IsAO2 n E := hD₄
    have hfun (x) : circuitFun n E x = f x := hfo x
    have hcorrect : circuitFun n E = graphFun G ∅ := by
      funext x
      apply Bool.eq_iff_iff.mpr
      constructor
      · intro hx
        exact hsound x ((hfun x).symm.trans hx)
      · intro hx
        obtain ⟨u, v, huv, hu, hv⟩ := (graph_true G x).mp hx
        refine circuit_monotone n E (ao_mono hE) (pairInput u v) x ?_ ?_
        · intro t ht
          rcases (show t = u ∨ t = v by simpa [pairInput] using ht) with rfl | rfl
          · exact hu
          · exact hv
        · exact (hfun _).trans (hpositive u v huv)
    have hmin := h.2.2 E hE hcorrect
    change C.gates.length ≤ D₄.gates.length at hmin
    rcases hbudget with hmany | hfalse
    · omega
    · have hZfalse : Z (fun _ => true) C.output = false := by
        cases he : Z (fun _ => true) C.output
        · rfl
        · have ht := (trimValueCompare C h.1 hW hzero k p (fun _ => true) C.output outBound).1 he
          rw [hfalse] at ht
          contradiction
      have hfree := hfree₂ (Or.inl (wireAvailableFalseOfTop hD₁
        (wireAvailablePreserved h₁ (hwires C.output outBound)) hZfalse))
      omega

theorem noOneJunkWithTrimmedTwoStars {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    (h4 : NoFourCycle G) {r a b : ℕ} (hJ : junk G C = {r})
    (hab : (gateAt C r).inputs = [a, b])
    {A B : Finset (Fin n)} (hA : RawForm C r a A false)
    (hB : RawForm C r b B false) (hdisj : Disjoint A B) (hcardA : 1 < A.card)
    {s d : Fin n} (hs : s ∈ A) (hd : d ∈ B)
    (hstarA : ∀ v ∈ B, G.Adj s v) (hstarB : ∀ u ∈ A, G.Adj u d)
    {W : (Fin n → Bool) → ℕ → Bool} (hW : EvalExcept n C r W)
    (hzero : ∀ x, W x (n + r) = false)
    (hlost : ∃ z ∈ A, W (pairInput z d) C.output = false)
    (hcover : ∀ u v, G.Adj u v → W (pairInput u v) C.output = true ∨
      (pairInput u v s = true ∧ hits B (pairInput u v)) ∨
      (pairInput u v d = true ∧ hits A (pairInput u v)))
    (readers : Finset ℕ) (hcount : 3 ≤ readers.card)
    (hread : ∀ j ∈ readers, j < C.gates.length ∧ n + r ∈ (gateAt C j).inputs) : False := by
  apply noOneJunkWithTrimmedTwoStarsBudget G C h hl h4 hJ hab hA hB hdisj hcardA
    hs hd hstarA hstarB hW hzero hlost hcover readers (by omega) (Or.inl hcount)
  intro i hi
  obtain ⟨hil, hm⟩ := hread i hi
  exact ⟨Nat.lt_of_add_lt_add_left (h.1.2.1 i hil _ hm), hil, n + r, hm, hzero _⟩

#print axioms noOneJunkWithTrimmedTwoStarsBudget

#print axioms noOneJunkWithTrimmedTwoStars

/-- Erasing the junk and folding its readers strictly reduces the gate count
    when every edge survives the suspension. -/
theorem noOneJunkWithoutLostEdges {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    {r : ℕ} (hJ : junk G C = {r})
    {W : (Fin n → Bool) → ℕ → Bool} (hW : EvalExcept n C r W)
    (hzero : ∀ x, W x (n + r) = false)
    (hcover : ∀ u v, G.Adj u v → W (pairInput u v) C.output = true) : False := by
  classical
  have hr := (junkMember G C hJ).1
  have hout := outputLast G C h (Nat.zero_lt_of_lt hr)
  have houtBound : C.output < n + C.gates.length := by omega
  obtain ⟨D₀, hao, hlen, hwires⟩ := compileFalseSuspension C h.1 hW hzero {r}
    (by simpa using hr) (by intro j hj; exact Or.inl (Finset.mem_singleton.mp hj))
  have hlen' : D₀.gates.length + 1 ≤ C.gates.length := by simpa using hlen
  rcases hwires C.output houtBound with hfalse | ⟨w, _, hwire⟩
  · have hnone (u v : Fin n) (huv : G.Adj u v) : False :=
      Bool.false_ne_true ((hfalse _).symm.trans (hcover u v huv))
    have := emptyGraphNoGates G C h hnone
    omega
  · let D : Circuit := ⟨D₀.gates, w⟩
    have hD : IsAO2 n D := hao
    have hval (x : Fin n → Bool) : circuitFun n D x = W x C.output := hwire x
    have hcorrect : circuitFun n D = graphFun G ∅ := by
      funext x
      apply Bool.eq_iff_iff.mpr
      refine ⟨fun hx => suspendedFalseSound G C h hl hJ hW hzero x ((hval x).symm.trans hx), ?_⟩
      intro hx
      obtain ⟨u, v, hadj, hu, hv⟩ := (graph_true G x).mp hx
      apply circuit_monotone n D (ao_mono hD) (pairInput u v) x ?_ ((hval _).trans (hcover u v hadj))
      intro t ht
      have he : t = u ∨ t = v := by simpa [pairInput] using ht
      rcases he with rfl | rfl
      · exact hu
      · exact hv
    have hmin := h.2.2 D hD hcorrect
    change C.gates.length ≤ D₀.gates.length at hmin
    omega

abbrev RepairStar (n : ℕ) := Fin n × Finset (Fin n)

abbrev RepairStar.centre {n : ℕ} (s : RepairStar n) : Fin n := s.1

abbrev RepairStar.support {n : ℕ} (s : RepairStar n) : Finset (Fin n) := s.2

def RepairStar.provider {n : ℕ} (s : RepairStar n) (x : Fin n → Bool) : Bool :=
  decide (∃ v ∈ s.support, x v = true)

def RepairStar.fires {n : ℕ} (s : RepairStar n) (x : Fin n → Bool) : Bool :=
  x s.centre && s.provider x

private theorem appendRepairStar {n : ℕ} (D : Circuit) (hD : IsAO2 n D)
    (f : (Fin n → Bool) → Bool) (hf : WireAvailable D f) (s : RepairStar n)
    (hprovider : WireAvailable D s.provider) :
    ∃ E : Circuit, IsAO2 n E ∧
      E.gates.length ≤ D.gates.length + 1 + (f (fun _ => true)).toNat ∧
      WireAvailable E (fun x => f x || s.fires x) ∧ PreservesWires n D E := by
  have hraw : WireAvailable D (fun x => x s.centre) :=
    Or.inr ⟨s.centre.val, by have := s.centre.isLt; omega, fun x =>
      (originalEvalExcept hD 0).1 x s.centre⟩
  obtain ⟨F, hF, hDF, hFlen, _, hstar⟩ := appendAvailableAnd D hD hraw hprovider
  change WireAvailable F s.fires at hstar
  obtain ⟨E, hE, hFE, hElen, hfree, hval⟩ :=
    appendAvailableOr F hF (wireAvailablePreserved hDF hf) hstar
  have hDE : PreservesWires n D E := ⟨hDF.1.trans hFE.1, fun x w hw =>
    (hFE.2 x w (by have := hDF.1; omega)).trans (hDF.2 x w hw)⟩
  refine ⟨E, hE, ?_, hval, hDE⟩
  cases htop : f (fun _ => true)
  · have := hfree (Or.inl (wireAvailableFalseOfTop hD hf htop))
    simp only [Bool.toNat_false, Nat.add_zero]
    omega
  · simp only [Bool.toNat_true]
    omega

/-- Compile a nonempty list of stars with at most two gates per star, saving
    one collector gate when the suspended output is identically false. -/
private theorem compileRepairStars {n : ℕ} (D : Circuit) (hD : IsAO2 n D)
    (f : (Fin n → Bool) → Bool) (hf : WireAvailable D f) (stars : List (RepairStar n))
    (hproviders : ∀ s ∈ stars, s.support.Nonempty ∧ WireAvailable D s.provider) :
    ∃ E : Circuit, IsAO2 n E ∧
      E.gates.length ≤ D.gates.length + 2 * stars.length ∧
      (stars ≠ [] → f (fun _ => true) = false → E.gates.length + 1 ≤ D.gates.length + 2 * stars.length) ∧
      WireAvailable E (fun x => f x || stars.any (fun s => s.fires x)) ∧
      (∀ g : (Fin n → Bool) → Bool, WireAvailable D g → WireAvailable E g) := by
  induction stars with
  | nil =>
    refine ⟨D, hD, by simp, by simp, ?_, fun _ hg => hg⟩
    simpa using hf
  | cons s ss ih =>
    obtain ⟨ds, hds, hlen, hbonus, hres, hpersist⟩ :=
      ih fun t ht => hproviders t (List.mem_cons_of_mem _ ht)
    obtain ⟨_, hp⟩ := hproviders s (by simp)
    let old := fun x => f x || ss.any (fun t => t.fires x)
    obtain ⟨fs, hfs, hcost, hval, hkeep⟩ :=
      appendRepairStar ds hds old hres s (hpersist s.provider hp)
    have hbit : (old (fun _ => true)).toNat ≤ 1 := by
      cases old (fun _ => true) <;> decide
    refine ⟨fs, hfs, by simp only [List.length_cons]; omega, ?_, ?_,
      fun g hg => wireAvailablePreserved hkeep (hpersist g hg)⟩
    · intro _ hf0
      simp only [List.length_cons]
      by_cases hempty : ss = []
      · have hb0 : (old (fun _ => true)).toNat = 0 := by simp [old, hempty, hf0]
        omega
      · have hprev := hbonus hempty hf0
        omega
    · simpa [old, Bool.or_left_comm, Bool.or_comm, Bool.or_assoc] using hval

/-- Realize a cover of the lost edge inputs by stars with available providers.
    The number of charged gates must exceed the cost of the repair. -/
theorem noOneJunkWithStarBudget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    {r : ℕ} (hJ : junk G C = {r})
    {W : (Fin n → Bool) → ℕ → Bool} (hW : EvalExcept n C r W)
    (hzero : ∀ x, W x (n + r) = false)
    (dropped : Finset ℕ) (hd : dropped ⊆ Finset.range C.gates.length)
    (hdrop : ∀ j ∈ dropped, j = r ∨
      ∃ w ∈ (gateAt C j).inputs, W (fun _ => true) w = false)
    (stars : List (RepairStar n)) (hne : stars ≠ [])
    (hproviders : ∀ s ∈ stars, s.support.Nonempty ∧
      ∃ p < n + C.gates.length, RawForm C r p s.support false)
    (hstarEdges : ∀ s ∈ stars, ∀ v ∈ s.support, G.Adj s.centre v)
    (hcover : ∀ u v, G.Adj u v → W (pairInput u v) C.output = true ∨
      stars.any (fun s => s.fires (pairInput u v)) = true)
    (hbudget : 2 * stars.length < dropped.card ∨
      (W (fun _ => true) C.output = false ∧ 2 * stars.length ≤ dropped.card)) : False := by
  have hr := (junkMember G C hJ).1
  have hout := outputLast G C h (Nat.zero_lt_of_lt hr)
  have houtBound : C.output < n + C.gates.length := by omega
  obtain ⟨D, hD, hlen, hwires⟩ := compileFalseSuspension C h.1 hW hzero dropped hd hdrop
  have hprov (s : RepairStar n) (hs : s ∈ stars) : s.support.Nonempty ∧ WireAvailable D s.provider := by
    obtain ⟨hn, p, hp, hP⟩ := hproviders s hs
    have he (x) : W x p = s.provider x := by
      apply Bool.eq_iff_iff.mpr
      simpa [RepairStar.provider] using hP.2 W hW x
    have hfun : (fun x => W x p) = s.provider := funext he
    exact ⟨hn, hfun ▸ hwires p hp⟩
  let f := fun x => W x C.output
  obtain ⟨fs, hfs, hcost, hbonus, hres, _⟩ :=
    compileRepairStars D hD f (hwires C.output houtBound) stars hprov
  have hsmall : fs.gates.length < C.gates.length := by
    rcases hbudget with hstrict | ⟨hfalse, hweak⟩
    · omega
    · have := hbonus hne hfalse
      omega
  rcases hres with hfalse | ⟨o, _, heval⟩
  · obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil stars hne
    obtain ⟨z, hz⟩ := (hproviders s hs).1
    have ht : s.fires (fun _ => true) = true := by
      simp only [RepairStar.fires, RepairStar.provider, Bool.true_and, decide_eq_true_eq]
      exact ⟨z, hz, trivial⟩
    have hsome : stars.any (fun s => s.fires (fun _ => true)) = true :=
      List.any_eq_true.mpr ⟨s, hs, ht⟩
    have ht' : (f (fun _ => true) || stars.any (fun s => s.fires (fun _ => true))) = false := hfalse _
    simp [hsome] at ht'
  · let E : Circuit := ⟨fs.gates, o⟩
    have hE : IsAO2 n E := hfs
    have hval (x) : circuitFun n E x = (f x || stars.any (fun s => s.fires x)) := heval x
    have hcorrect : circuitFun n E = graphFun G ∅ := by
      funext x
      apply Bool.eq_iff_iff.mpr
      constructor
      · intro hx
        rw [hval, Bool.or_eq_true] at hx
        rcases hx with hy | hstars
        · exact suspendedFalseSound G C h hl hJ hW hzero x hy
        · obtain ⟨s, hs, hfire⟩ := List.any_eq_true.mp hstars
          obtain ⟨hc, v, hv, hvx⟩ : x s.centre = true ∧ ∃ v ∈ s.support, x v = true := by
            simpa [RepairStar.fires, RepairStar.provider] using hfire
          exact (graph_true G x).mpr ⟨s.centre, v, hstarEdges s hs v hv, hc, hvx⟩
      · intro hx
        obtain ⟨u, v, huv, hu, hv⟩ := (graph_true G x).mp hx
        apply circuit_monotone n E (ao_mono hE) (pairInput u v) x ?_ ?_
        · intro t ht
          have he : t = u ∨ t = v := by simpa [pairInput] using ht
          rcases he with rfl | rfl
          · exact hu
          · exact hv
        · change circuitFun n E (pairInput u v) = true
          rw [hval, Bool.or_eq_true]
          exact hcover u v huv
    have hmin := h.2.2 E hE hcorrect
    change C.gates.length ≤ fs.gates.length at hmin
    exact (Nat.not_lt_of_ge hmin) hsmall

/-- Two immediate readers pay for a strict one-star repair. The provider is
    preserved by the fold, so the repair uses at most one AND and one OR. -/
theorem noOneJunkOneStarWithTwoReaders {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    {r : ℕ} (hJ : junk G C = {r})
    {W : (Fin n → Bool) → ℕ → Bool} (hW : EvalExcept n C r W)
    (hzero : ∀ x, W x (n + r) = false)
    {j k : ℕ} (hj : j < C.gates.length) (hk : k < C.gates.length) (hjk : j ≠ k)
    (hjr : n + r ∈ (gateAt C j).inputs) (hkr : n + r ∈ (gateAt C k).inputs)
    {p : ℕ} (hp : p < n + C.gates.length) {S : Finset (Fin n)} (hS : RawForm C r p S false)
    (hne : S.Nonempty) (c : Fin n) (hadj : ∀ v ∈ S, G.Adj c v)
    (hcover : ∀ u v, G.Adj u v → W (pairInput u v) C.output = true ∨
      (pairInput u v c = true ∧ ∃ w ∈ S, pairInput u v w = true)) : False := by
  classical
  have hr := (junkMember G C hJ).1
  have hjr' : r ≠ j := by have := h.1.2.1 j hj _ hjr; omega
  have hkr' : r ≠ k := by have := h.1.2.1 k hk _ hkr; omega
  let star : RepairStar n := ⟨c, S⟩
  refine noOneJunkWithStarBudget G C h hl hJ hW hzero {r, j, k} ?_ ?_ [star]
    (by simp) ?_ ?_ ?_ ?_
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl <;> exact Finset.mem_range.mpr (by assumption)
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr ⟨n + r, hjr, hzero _⟩
    · exact Or.inr ⟨n + r, hkr, hzero _⟩
  · intro s hs
    have he : s = star := by simpa using hs
    subst s
    exact ⟨hne, p, hp, hS⟩
  · intro s hs
    have he : s = star := by simpa using hs
    subst s
    exact hadj
  · intro u v huv
    simpa [star, RepairStar.fires, RepairStar.provider] using hcover u v huv
  · left
    simp [hjr', hkr', hjk]

#print axioms noOneJunkWithoutLostEdges
#print axioms noOneJunkWithStarBudget
#print axioms noOneJunkOneStarWithTwoReaders


/-- Even one direct AND reader pays for a one-star repair: if the
    suspended output survives, a distinct clean OR reader folds. -/
theorem noOneJunkOneStarWithAndReader {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    {r j : ℕ} (hJ : junk G C = {r})
    {W : (Fin n → Bool) → ℕ → Bool} (hW : EvalExcept n C r W)
    (hzero : ∀ x, W x (n+r) = false)
    (hj : j < C.gates.length) (hread : n+r ∈ (gateAt C j).inputs)
    (hand : (gateAt C j).op = GateOp.and)
    {p : ℕ} (hp : p < n + C.gates.length) {S : Finset (Fin n)}
    (hS : RawForm C r p S false) (hne : S.Nonempty)
    (c : Fin n) (hadj : ∀ v ∈ S, G.Adj c v)
    (hcover : ∀ u v, G.Adj u v → W (pairInput u v) C.output = true ∨
      (pairInput u v c = true ∧ ∃ w ∈ S, pairInput u v w = true)) : False := by
  classical
  have hr := (junkMember G C hJ).1
  have hrj : r < j := Nat.lt_of_add_lt_add_left (h.1.2.1 j hj _ hread)
  let star : RepairStar n := ⟨c,S⟩
  have hprov : ∀ s ∈ [star], s.support.Nonempty ∧
      ∃ p < n + C.gates.length, RawForm C r p s.support false := by
    intro s hs
    have he : s = star := by simpa using hs
    subst s
    exact ⟨hne,p,hp,hS⟩
  have hedges : ∀ s ∈ [star], ∀ v ∈ s.support, G.Adj s.centre v := by
    intro s hs
    have he : s = star := by simpa using hs
    subst s
    exact hadj
  have hcov : ∀ u v, G.Adj u v → W (pairInput u v) C.output = true ∨
      [star].any (fun s => s.fires (pairInput u v)) = true := by
    intro u v huv
    simpa [star,RepairStar.fires,RepairStar.provider] using hcover u v huv
  by_cases hout : W (fun _ => true) C.output = false
  · refine noOneJunkWithStarBudget G C h hl hJ hW hzero {r,j} ?_ ?_ [star]
      (by simp) hprov hedges hcov ?_
    · intro t ht
      rcases (show t = r ∨ t = j by simpa using ht) with rfl | rfl
      · exact Finset.mem_range.mpr hr
      · exact Finset.mem_range.mpr hj
    · intro t ht
      rcases (show t = r ∨ t = j by simpa using ht) with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr ⟨n+r,hread,hzero _⟩
    · right
      exact ⟨hout,by simp [hrj.ne]⟩
  · have htop : W (fun _ => true) C.output = true := by
      cases he : W (fun _ => true) C.output <;> simp_all
    obtain ⟨a,b,hab⟩ := twoOperands h.1 hj
    have hjzero : W (fun _ => true) (n+j) = false := by
      cases he : W (fun _ => true) (n+j)
      · rfl
      · obtain ⟨ha,hb⟩ := (evalExcept_and hW hj hrj.ne.symm hand hab _).mp he
        have he' : n+r = a ∨ n+r = b := by simpa [hab] using hread
        rcases he' with he' | he'
        · rw [← he',hzero] at ha
          cases ha
        · rw [← he',hzero] at hb
          cases hb
    have hneout : C.output ≠ n+j := by
      intro he
      rw [he,hjzero] at htop
      cases htop
    obtain ⟨k,hjk,hk,hkr⟩ := noUnreadGate G C h j (n+r) hj
      (h.1.2.1 j hj _ hread) hneout
    have hrk : r < k := hrj.trans hjk
    refine noOneJunkWithStarBudget G C h hl hJ hW hzero {r,j,k} ?_ ?_ [star]
      (by simp) hprov hedges hcov ?_
    · intro t ht
      simp only [Finset.mem_insert,Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl <;> exact Finset.mem_range.mpr (by assumption)
    · intro t ht
      simp only [Finset.mem_insert,Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr ⟨n+r,hread,hzero _⟩
      · exact Or.inr ⟨n+j,hkr,hjzero⟩
    · left
      simp [hrj.ne,hrk.ne,hjk.ne]

/-- A mixed-colour raw provider cannot support any surviving clean
    product. This is the exclusivity criterion needed by the sole-AND
    two-star branch. -/
theorem mixedProviderNoResidualUse {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    (colour : Fin n → Bool) (hcolour : ∀ u v, G.Adj u v → colour u ≠ colour v)
    {r w : ℕ} (hJ : junk G C = {r})
    {W : (Fin n → Bool) → ℕ → Bool} (hW : EvalExcept n C r W)
    (hzero : ∀ x, W x (n+r) = false)
    {S : Finset (Fin n)} (hS : RawForm C r w S false)
    {u v : Fin n} (hu : u ∈ S) (hv : v ∈ S) (hmix : colour u ≠ colour v) :
    ¬ ResidualUse G C r (W (fun _ => true)) w := by
  intro huse
  obtain ⟨d, hd⟩ := residualUseCoversSupport G C h hl hJ hW hzero huse
    (fun x hx => (hS.2 W hW x).mpr (Or.inl hx))
  have h1 := hcolour u d (hd u hu).1
  have h2 := hcolour v d (hd v hv).1
  generalize colour u = cu at h1 hmix
  generalize colour v = cv at h2 hmix
  generalize colour d = cd at h1 h2
  cases cu <;> cases cv <;> cases cd <;> simp_all

#print axioms noOneJunkOneStarWithAndReader
#print axioms mixedProviderNoResidualUse


/-- If the junk has no direct OR reader, every other dirty wire
    has a raw-only representation, valid under arbitrary suspension. -/
theorem dirtyRawFormNoOrReader {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    {r : ℕ} (hJ : junk G C = {r})
    (hno : ∀ j < C.gates.length, (gateAt C j).op = GateOp.or →
      n+r ∉ (gateAt C j).inputs) :
    ∀ w < n+C.gates.length, w ≠ n+r → ¬ CleanWire G C w →
      ∃ S : Finset (Fin n), RawForm C r w S false := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hne hd
    by_cases hn : w < n
    · refine ⟨{⟨w,hn⟩},by simp,?_⟩
      intro V hV x
      rw [hV.1 x ⟨w,hn⟩]
      simp
    · obtain ⟨j,rfl⟩ : ∃ j, w = n+j := ⟨w-n,by omega⟩
      have hj : j < C.gates.length := by omega
      have hjr : j ≠ r := by omega
      have hor : (gateAt C j).op = GateOp.or := by
        rcases h.1.1 _ (gateAt_mem hj) with hand | ho
        · exact (hjr (uniqueDirtyAnd G C hJ hj hd hand)).elim
        · exact ho
      obtain ⟨a,b,hab⟩ := twoOperands h.1 hj
      have hma : a ∈ (gateAt C j).inputs := by simp [hab]
      have hmb : b ∈ (gateAt C j).inputs := by simp [hab]
      have ha := h.1.2.1 j hj a hma
      have hb := h.1.2.1 j hj b hmb
      have hda : ¬ CleanWire G C a :=
        fun hc => hd (cleanWireReader G C h hl hj hma hc).2
      have hdb : ¬ CleanWire G C b :=
        fun hc => hd (cleanWireReader G C h hl hj hmb hc).2
      obtain ⟨A,hA⟩ := ih a ha (by omega) (fun he => hno j hj hor (he ▸ hma)) hda
      obtain ⟨B,hB⟩ := ih b hb (by omega) (fun he => hno j hj hor (he ▸ hmb)) hdb
      refine ⟨A∪B,by simp,?_⟩
      intro V hV x
      have hAs : V x a = true ↔ hits A x := by simpa [hits] using hA.2 V hV x
      have hBs : V x b = true ↔ hits B x := by simpa [hits] using hB.2 V hV x
      rw [evalExcept_or hV hj hjr hor x, hab]
      constructor
      · rintro ⟨v,hv,ht⟩
        have he : v = a ∨ v = b := by simpa using hv
        rcases he with rfl | rfl
        · obtain ⟨z,hz,hzx⟩ := hAs.mp ht
          exact Or.inl ⟨z,Finset.mem_union.mpr (Or.inl hz),hzx⟩
        · obtain ⟨z,hz,hzx⟩ := hBs.mp ht
          exact Or.inl ⟨z,Finset.mem_union.mpr (Or.inr hz),hzx⟩
      · rintro (⟨z,hz,hzx⟩ | ⟨hf,_⟩)
        · rcases Finset.mem_union.mp hz with hz | hz
          · exact ⟨a,by simp,hAs.mpr ⟨z,hz,hzx⟩⟩
          · exact ⟨b,by simp,hBs.mpr ⟨z,hz,hzx⟩⟩
        · cases hf

/-- Without an immediate OR reader, all clean AND gates that do not
    read the junk directly are unchanged by suspension. -/
theorem cleanTopUnaffectedNoOrReader {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    {r j : ℕ} (hJ : junk G C = {r})
    (hno : ∀ i < C.gates.length, (gateAt C i).op = GateOp.or →
      n+r ∉ (gateAt C i).inputs)
    (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and)
    (hc : BelowF G C j) (hnread : n+r ∉ (gateAt C j).inputs)
    {V W : (Fin n → Bool) → ℕ → Bool}
    (hV : EvalExcept n C r V) (hW : EvalExcept n C r W)
    (x : Fin n → Bool) : V x (n+j) = W x (n+j) := by
  have hdiff := cleanDifferent G C hJ hc
  rw [hV.2 x j hj hdiff,hW.2 x j hj hdiff]
  congr 1
  apply List.map_congr_left
  intro p hp
  have hlt := h.1.2.1 j hj p hp
  obtain ⟨S,hS⟩ := dirtyRawFormNoOrReader G C h hl hJ hno p (by omega)
    (fun he => hnread (he ▸ hp)) (noCleanAndOperand G C h j p hj hp hand)
  apply Bool.eq_iff_iff.mpr
  have hVraw : V x p = true ↔ hits S x := by simpa [hits] using hS.2 V hV x
  have hWraw : W x p = true ↔ hits S x := by simpa [hits] using hS.2 W hW x
  exact hVraw.trans hWraw.symm

#print axioms dirtyRawFormNoOrReader
#print axioms cleanTopUnaffectedNoOrReader


/-- Additional operand suppression cannot increase any wire. The two
    evaluations use the same suspended junk value. -/
private theorem maskedValueLe {n : ℕ} (C : Circuit) (h : IsAO2 n C)
    (r : ℕ) (M N : ℕ → ℕ → Bool)
    (hm : ∀ j w, M j w = true → N j w = true)
    (fill : (Fin n → Bool) → Bool) (x : Fin n → Bool) :
    ∀ w < n + C.gates.length,
      maskedValue C r N fill x w = true → maskedValue C r M fill x w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw ht
    by_cases hraw : w < n
    · let v : Fin n := ⟨w,hraw⟩
      rw [maskedValue_raw C r N fill x v] at ht
      rw [maskedValue_raw C r M fill x v]
      exact ht
    obtain ⟨j,rfl⟩ : ∃ j, w = n+j := ⟨w-n,by omega⟩
    by_cases hjr : j = r
    · subst j
      rw [maskedValue_hole C r N fill x] at ht
      rw [maskedValue_hole C r M fill x]
      exact ht
    have hj : j < C.gates.length := by omega
    rw [maskedValue_gate C h r N fill x hj hjr] at ht
    rw [maskedValue_gate C h r M fill x hj hjr]
    have hi (v) (hv : v ∈ (gateAt C j).inputs)
        (he : (if N j v then false else maskedValue C r N fill x v) = true) :
        (if M j v then false else maskedValue C r M fill x v) = true := by
      have hn : N j v = false := by
        cases hh : N j v <;> simp_all
      have hm' : M j v = false := by
        cases hh : M j v
        · rfl
        · have hz := hm j v hh
          rw [hn] at hz
          contradiction
      have he' : maskedValue C r N fill x v = true := by simpa [hn] using he
      have hlt := h.2.1 j hj v hv
      simpa [hm'] using ih v hlt (by omega) he'
    rcases h.1 _ (gateAt_mem hj) with hand | hor
    · simp only [hand,GateOp.eval,List.all_map,List.all_eq_true,Function.comp_apply] at ht ⊢
      exact fun v hv => hi v hv (ht v hv)
    · simp only [hor,GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply] at ht ⊢
      obtain ⟨v,hv,he⟩ := ht
      exact ⟨v,hv,hi v hv he⟩

/-- A second mask concentrated at q leaves a pre-junk pure provider
    unchanged if a singleton witnesses that q cannot feed it. This
    holds even when the first mask has already trimmed another provider. -/
private theorem extraMaskPreservesProvider {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    {r q : ℕ} (hJ : junk G C = {r}) {W : (Fin n → Bool) → ℕ → Bool}
    (hW : EvalExcept n C r W) (s : Fin n)
    (hq : W (pairInput s s) (n+q) = true)
    (M N : ℕ → ℕ → Bool) (hm : ∀ j w, j ≠ q → N j w = M j w)
    (fill : (Fin n → Bool) → Bool) (x : Fin n → Bool) :
    ∀ w < n+r, ¬ CleanWire G C w → W (pairInput s s) w = false →
      maskedValue C r N fill x w = maskedValue C r M fill x w := by
  have hr := (junkMember G C hJ).1
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hd hfalse
    by_cases hraw : w < n
    · let v : Fin n := ⟨w,hraw⟩
      exact (maskedValue_raw C r N fill x v).trans (maskedValue_raw C r M fill x v).symm
    obtain ⟨j,rfl⟩ : ∃ j, w = n+j := ⟨w-n,by omega⟩
    have hj : j < C.gates.length := by omega
    have hjr : j ≠ r := by omega
    have hjq : j ≠ q := by
      rintro rfl
      exact Bool.noConfusion (hfalse.symm.trans hq)
    have hor : (gateAt C j).op = GateOp.or := by
      rcases h.1.1 _ (gateAt_mem hj) with hand | ho
      · exact (hjr (uniqueDirtyAnd G C hJ hj hd hand)).elim
      · exact ho
    rw [maskedValue_gate C h.1 r N fill x hj hjr,
      maskedValue_gate C h.1 r M fill x hj hjr]
    congr 1
    apply List.map_congr_left
    intro v hv
    have hlt := h.1.2.1 j hj v hv
    have hvd : ¬ CleanWire G C v := fun hc =>
      hd (cleanWireReader G C h hl hj hv hc).2
    have hvfalse : W (pairInput s s) v = false := by
      cases he : W (pairInput s s) v
      · rfl
      · exact Bool.noConfusion (hfalse.symm.trans
          ((evalExcept_or hW hj hjr hor (pairInput s s)).mpr ⟨v,hv,he⟩))
    rw [hm j v hjq, ih v hlt (hlt.trans hw) hvd hvfalse]

/-- An active dirty pre-junk ancestor forces its value through the OR
    cone of a dirty provider. -/
private theorem preJunkConeTrue {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    {r : ℕ} (hJ : junk G C = {r}) {W : (Fin n → Bool) → ℕ → Bool}
    (hW : EvalExcept n C r W) (x : Fin n → Bool) :
    ∀ j < r, ¬ CleanWire G C (n+j) → ∀ k, (k = j ∨ InCone n C k j) →
      W x (n+k) = true → W x (n+j) = true := by
  have hr := (junkMember G C hJ).1
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj hd k hk hv
    rcases hk with rfl | hk
    · exact hv
    have hjl := hj.trans hr
    have hjr := hj.ne
    have hor : (gateAt C j).op = GateOp.or := by
      rcases h.1.1 _ (gateAt_mem hjl) with hand | ho
      · exact (hjr (uniqueDirtyAnd G C hJ hjl hd hand)).elim
      · exact ho
    obtain ⟨w,hm,hn,hw,hpath⟩ := (coneRec hjl k).mp hk
    obtain ⟨i,rfl⟩ : ∃ i, w = n+i := ⟨w-n,by omega⟩
    have hid : ¬ CleanWire G C (n+i) := fun hc =>
      hd (cleanWireReader G C h hl hjl hm hc).2
    have hpath' : k = i ∨ InCone n C k i := by simpa using hpath
    exact (evalExcept_or hW hjl hjr hor x).mpr
      ⟨n+i,hm,ih i (by omega) (by omega) hid k hpath' hv⟩

#print axioms maskedValueLe
#print axioms extraMaskPreservesProvider
#print axioms preJunkConeTrue

/-- Two-star repair with an additional exclusive provider that activates
    on both exposed centres. Masking that provider saves one more gate,
    while singleton separation preserves both pre-junk providers. -/
theorem noOneJunkWithMixedProviderAndTrim {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    (h4 : NoFourCycle G) {r a b : ℕ} (hJ : junk G C = {r})
    (hab : (gateAt C r).inputs = [a, b])
    {A B : Finset (Fin n)} (hA : RawForm C r a A false)
    (hB : RawForm C r b B false) (hdisj : Disjoint A B) (hcardA : 1 < A.card)
    {s d : Fin n} (hs : s ∈ A) (hd : d ∈ B)
    (hstarA : ∀ v ∈ B, G.Adj s v) (hstarB : ∀ u ∈ A, G.Adj u d)
    {W : (Fin n → Bool) → ℕ → Bool} (hW : EvalExcept n C r W)
    (hzero : ∀ x, W x (n + r) = false)
    (hlost : ∃ z ∈ A, W (pairInput z d) C.output = false)
    (hcover : ∀ u v, G.Adj u v → W (pairInput u v) C.output = true ∨
      (pairInput u v s = true ∧ hits B (pairInput u v)) ∨
      (pairInput u v d = true ∧ hits A (pairInput u v)))
    {q : ℕ} (hq : q < C.gates.length) (hqr : q ≠ r)
    (hqd : ¬ CleanWire G C (n+q))
    (hqu : ¬ ResidualUse G C r (W (fun _ => true)) (n+q))
    (hqs : W (pairInput s s) (n+q) = true)
    (hqt : W (pairInput d d) (n+q) = true)
    (charges : Finset ℕ) (hqn : q ∉ charges) (hcount : 1 ≤ charges.card)
    (hbudget : 2 ≤ charges.card ∨ W (fun _ => true) C.output = false)
    (hcharge : ∀ i ∈ charges, r < i ∧ i < C.gates.length ∧
      ∃ w ∈ (gateAt C i).inputs, W (fun _ => true) w = false) : False := by
  classical
  obtain ⟨hr, hand, _⟩ := junkMember G C hJ
  have ham : a ∈ (gateAt C r).inputs := by simp [hab]
  have hbm : b ∈ (gateAt C r).inputs := by simp [hab]
  have hal := h.1.2.1 r hr a ham
  have hbl := h.1.2.1 r hr b hbm
  have had := noCleanAndOperand G C h r a hr ham hand
  have hbd := noCleanAndOperand G C h r b hr hbm hand
  have hsemA (x) : W x a = true ↔ hits A x := by simpa [hits] using hA.2 W hW x
  have hsemB (x) : W x b = true ↔ hits B x := by simpa [hits] using hB.2 W hW x
  have hna : n ≤ a := by
    by_contra! hraw
    let u : Fin n := ⟨a, hraw⟩
    obtain ⟨v, hv, w, hw, hne⟩ := Finset.one_lt_card.mp hcardA
    have ident (z) (hz : z ∈ A) : u = z := by
      have ht := (hsemA (pairInput z z)).mpr ⟨z, hz, by simp [pairInput]⟩
      simpa [pairInput] using (hW.1 (pairInput z z) u).symm.trans ht
    exact hne ((ident v hv).symm.trans (ident w hw))
  obtain ⟨j, rfl⟩ : ∃ j, a = n + j := ⟨a - n, by omega⟩
  obtain ⟨z, hz, hmissing⟩ := hlost
  obtain ⟨k, hk, hpath, hku, hkd, hko, p, hp, hpactive, hpform⟩ :=
    residualStarTrimBoundary G C h hl h4 hJ (by omega) had hA hstarB hs hz hW hzero hmissing
  have hkr : k < r := by omega
  have hkl := hkr.trans hr
  have hks := (evalExcept_or hW hkl hkr.ne hko (pairInput s s)).mpr ⟨p, hp, hpactive⟩
  have hbs : W (pairInput s s) b = false := by
    cases he : W (pairInput s s) b
    · rfl
    · obtain ⟨v, hv, hvx⟩ := (hsemB _).mp he
      have heq : v = s := by simpa [pairInput] using hvx
      exact (Finset.disjoint_left.mp hdisj hs (heq ▸ hv)).elim
  have had0 : W (pairInput d d) (n+j) = false := by
    cases he : W (pairInput d d) (n+j)
    · rfl
    · obtain ⟨v,hv,hvx⟩ := (hsemA _).mp he
      have heq : v = d := by simpa [pairInput] using hvx
      exact (Finset.disjoint_left.mp hdisj (heq ▸ hv) hd).elim
  have hkq : k ≠ q := by
    intro he
    have ht : W (pairInput d d) (n+k) = true := by simpa [he] using hqt
    have ht' := preJunkConeTrue G C h hl hJ hW (pairInput d d) j (by omega) had k hpath ht
    rw [had0] at ht'
    contradiction
  let M := trimOperand k p
  let N := fun i w => M i w || decide (i = q)
  let Z₀ := trimValue (n := n) C r k p
  let Z := maskedValue (n := n) C r N (fun _ => false)
  have hZraw := maskedValue_raw C r N (fun _ : Fin n → Bool => false)
  have hZzero := maskedValue_hole C r N (fun _ : Fin n → Bool => false)
  have hZgate (x) (i) (hi : i < C.gates.length) (hir : i ≠ r) :=
    maskedValue_gate C h.1 r N (fun _ : Fin n → Bool => false) x hi hir
  have hmask (i w : ℕ) (hi : i ≠ q) : N i w = M i w := by
    simp [N,hi]
  have hZle (x) (w) (hw : w < n+C.gates.length) (ht : Z x w = true) :
      W x w = true := by
    apply (trimValueCompare C h.1 hW hzero k p x w hw).1
    exact maskedValueLe C h.1 r M N (by intro i v hv; simp [N,hv])
      (fun _ => false) x w hw ht
  have hkeep : ∀ x, W x C.output = true → Z x C.output = true := by
    apply residualOutputPreserved G C h hl hJ hW hzero hZraw hZzero
    intro x i hi hir hu
    have hik : i ≠ k := by
      rintro rfl
      exact hu.elim hkd hku
    have hiq : i ≠ q := by
      rintro rfl
      exact hu.elim hqd hqu
    simpa [N,M,trimOperand,hik,hiq] using hZgate x i hi hir
  have hZA (x) : Z x (n+j) = Z₀ x (n+j) :=
    extraMaskPreservesProvider G C h hl hJ hW d hqt M N hmask
      (fun _ => false) x (n+j) hal had had0
  have hZB (x) : Z x b = W x b := by
    have he : Z x b = Z₀ x b := extraMaskPreservesProvider G C h hl hJ hW s hqs
      M N hmask (fun _ => false) x b hbl hbd hbs
    exact he.trans (trimValuePreservesOtherProvider G C h hl hJ hW s hks x b hbl hbd hbs)
  have outBound : C.output < n + C.gates.length := by
    have := outputLast G C h (by omega : 0 < C.gates.length)
    omega
  have habound : n + j < n + C.gates.length := by omega
  have hbbound : b < n + C.gates.length := by omega
  let f (x : Fin n → Bool) := (Z x C.output || (x s && Z x b)) || (x d && Z x (n + j))
  have hpositive (u v : Fin n) (huv : G.Adj u v) : f (pairInput u v) = true := by
    let x := pairInput u v
    have leftStar (hc : x s = true) (hb : hits B x) : f x = true := by
      simp [f, hc, hZB x, (hsemB x).mpr hb]
    have base (ho : W x C.output = true) : f x = true := by
      simp [f, hkeep x ho]
    rcases hcover u v huv with ho | ⟨hcs, hb⟩ | ⟨hcd, ha⟩
    · exact base ho
    · exact leftStar hcs hb
    obtain ⟨t, ht, htx⟩ := ha
    have htd := G.ne_of_adj (hstarB t ht)
    have hpair : x = pairInput t d := by
      have htuv : t = u ∨ t = v := by simpa [x, pairInput] using htx
      have hduv : d = u ∨ d = v := by simpa [x, pairInput] using hcd
      rcases htuv with ht' | ht' <;> rcases hduv with hd' | hd'
      · exact (htd (ht'.trans hd'.symm)).elim
      · simp [x, ht', hd']
      · simpa [x, ht', hd'] using pairInputComm u v
      · exact (htd (ht'.trans hd'.symm)).elim
    cases hpv : W x p
    · have he := (trimValueCompare C h.1 hW hzero k p x (n + j) habound).2 hpv
      have haz : Z x (n + j) = true := (hZA x).trans (he.trans ((hsemA x).mpr ⟨t, ht, htx⟩))
      change ((Z x C.output || (x s && Z x b)) || (x d && Z x (n + j))) = true
      have hxd : x d = true := hcd
      rw [hxd, haz]
      simp
    · rcases hpform with rfl | ⟨Q, hQ, _, hQA, _, hQcover⟩
      · have hsx : x s = true := (hW.1 x s).symm.trans hpv
        exact leftStar hsx ⟨d, hd, hcd⟩
      · obtain ⟨q, hq, hqx⟩ := ((hQ.2 W hW x).mp hpv).resolve_right (by simp)
        have hqtd : q = t ∨ q = d := by simpa [hpair, pairInput] using hqx
        have hqd : q ≠ d := G.ne_of_adj (hstarB q (hQA hq))
        have hqt := hqtd.resolve_right hqd
        exact base (by rw [hpair, ← hqt]; exact hQcover q hq)
  have hsound (x) (hx : f x = true) : graphFun G ∅ x = true := by
    simp only [f, Bool.or_eq_true, Bool.and_eq_true] at hx
    rcases hx with (ho | ⟨hx, hb⟩) | ⟨hx, ha⟩
    · exact suspendedFalseSound G C h hl hJ hW hzero x
        (hZle x C.output outBound ho)
    · obtain ⟨v, hv, hvx⟩ := (hsemB x).mp ((hZB x).symm.trans hb)
      exact (graph_true G x).mpr ⟨s, v, hstarA v hv, hx, hvx⟩
    · obtain ⟨u, hu, hux⟩ := (hsemA x).mp
        (hZle x (n+j) habound ha)
      exact (graph_true G x).mpr ⟨u, d, hstarB u hu, hux, hx⟩
  have hrnot : r ∉ charges := fun hm => (Nat.lt_irrefl r) (hcharge r hm).1
  have hknot : k ∉ insert r charges := by
    intro hm
    rcases Finset.mem_insert.mp hm with he | hm
    · omega
    · have := (hcharge k hm).1
      omega
  have hqnot : q ∉ insert k (insert r charges) := by
    intro hm
    rcases Finset.mem_insert.mp hm with he | hm
    · exact hkq he.symm
    · rcases Finset.mem_insert.mp hm with he | hm
      · exact hqr he
      · exact hqn hm
  let dropped := insert q (insert k (insert r charges))
  have hsize : dropped.card = charges.card + 3 := by
    rw [show dropped = insert q (insert k (insert r charges)) from rfl,
      Finset.card_insert_of_notMem hqnot, Finset.card_insert_of_notMem hknot,
      Finset.card_insert_of_notMem hrnot]
  obtain ⟨D, hD, hlen, hwires⟩ := compileMaskedSuspension C h.1 N
    Z hZraw hZgate hZzero dropped (by
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact Finset.mem_range.mpr hq
      · rcases Finset.mem_insert.mp hi with rfl | hi
        · exact Finset.mem_range.mpr hkl
        · rcases Finset.mem_insert.mp hi with rfl | hi
          · exact Finset.mem_range.mpr hr
          · exact Finset.mem_range.mpr (hcharge i hi).2.1) (by
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · obtain ⟨u,v,huv⟩ := twoOperands h.1 hq
        exact Or.inr ⟨u,by simp [huv],Or.inl (by simp [N])⟩
      · rcases Finset.mem_insert.mp hi with rfl | hi
        · exact Or.inr ⟨p, hp, Or.inl (by simp [N,M,trimOperand])⟩
        · rcases Finset.mem_insert.mp hi with rfl | hi
          · exact Or.inl rfl
          · obtain ⟨w, hw, hz⟩ := (hcharge i hi).2.2
            have hwb : w < n + C.gates.length :=
              (h.1.2.1 i (hcharge i hi).2.1 w hw).trans
                (Nat.add_lt_add_left (hcharge i hi).2.1 n)
            have hz' : Z (fun _ => true) w = false := by
              cases he : Z (fun _ => true) w
              · rfl
              · have ht := hZle (fun _ => true) w hwb he
                rw [hz] at ht
                contradiction
            exact Or.inr ⟨w, hw, Or.inr hz'⟩)
  have rawAvailable (F : Circuit) (hF : IsAO2 n F) (v : Fin n) :
      WireAvailable F (fun x => x v) :=
    Or.inr ⟨v, by have := v.isLt; omega, fun x => (originalEvalExcept hF r).1 x v⟩
  obtain ⟨D₁, hD₁, h₁, hlen₁, _, hs₁⟩ :=
    appendAvailableAnd D hD (rawAvailable D hD s) (hwires b hbbound)
  obtain ⟨D₂, hD₂, h₂, hlen₂, hfree₂, hs₂⟩ :=
    appendAvailableOr D₁ hD₁ (wireAvailablePreserved h₁ (hwires C.output outBound)) hs₁
  obtain ⟨D₃, hD₃, h₃, hlen₃, _, hs₃⟩ := appendAvailableAnd D₂ hD₂ (rawAvailable D₂ hD₂ d)
    (wireAvailablePreserved h₂ (wireAvailablePreserved h₁ (hwires (n + j) habound)))
  obtain ⟨D₄, hD₄, _, hlen₄, _, hf⟩ :=
    appendAvailableOr D₃ hD₃ (wireAvailablePreserved h₃ hs₂) hs₃
  change WireAvailable D₄ f at hf
  rcases hf with hf | ⟨o, _, hfo⟩
  · exact Bool.noConfusion ((hf _).symm.trans (hpositive s d (hstarA d hd)))
  · let E : Circuit := ⟨D₄.gates, o⟩
    have hE : IsAO2 n E := hD₄
    have hfun (x) : circuitFun n E x = f x := hfo x
    have hcorrect : circuitFun n E = graphFun G ∅ := by
      funext x
      apply Bool.eq_iff_iff.mpr
      constructor
      · intro hx
        exact hsound x ((hfun x).symm.trans hx)
      · intro hx
        obtain ⟨u, v, huv, hu, hv⟩ := (graph_true G x).mp hx
        refine circuit_monotone n E (ao_mono hE) (pairInput u v) x ?_ ?_
        · intro t ht
          rcases (show t = u ∨ t = v by simpa [pairInput] using ht) with rfl | rfl
          · exact hu
          · exact hv
        · exact (hfun _).trans (hpositive u v huv)
    have hmin := h.2.2 E hE hcorrect
    change C.gates.length ≤ D₄.gates.length at hmin
    rcases hbudget with hmany | hfalse
    · omega
    · have hZfalse : Z (fun _ => true) C.output = false := by
        cases he : Z (fun _ => true) C.output
        · rfl
        · have ht := hZle (fun _ => true) C.output outBound he
          rw [hfalse] at ht
          contradiction
      have hfree := hfree₂ (Or.inl (wireAvailableFalseOfTop hD₁
        (wireAvailablePreserved h₁ (hwires C.output outBound)) hZfalse))
      omega

#print axioms noOneJunkWithMixedProviderAndTrim


/-- The decisive geometry of an indispensable noncentral star edge.
    Two tops sharing a raw carrier leaf, one exposing the centre s,
    must both use only s on their opposite side.  Unlike a bare
    common-neighbour condition, this uses the actual suspended output:
    the shared raw leaf cannot already cover the missing edge s-v.
    No claim about identifying the shared carrier path is assumed here. -/
private theorem indispensableCarrierOppositeSingletonOfProduct {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    (h4 : NoFourCycle G) (colour : Fin n → Bool)
    (hcolour : ∀ u v, G.Adj u v → colour u ≠ colour v)
    {r : ℕ} (hJ : junk G C = {r})
    {A B : Finset (Fin n)}
    (hprod : ∀ x : Fin n → Bool, val C (List.ofFn x) (n+r) = true ↔ hits A x ∧ hits B x)
    (hcardA : 1 < A.card)
    {s d v : Fin n} (hs : s ∈ A) (hv : v ∈ B) (hvd : v ≠ d)
    (hstarA : ∀ z ∈ B, G.Adj s z) (hstarB : ∀ z ∈ A, G.Adj d z)
    {W : (Fin n → Bool) → ℕ → Bool} (hW : EvalExcept n C r W)
    (hmiss : W (pairInput s v) C.output = false)
    {i j : ℕ} (hi : i < C.gates.length) (hia : (gateAt C i).op = GateOp.and)
    (hic : BelowF G C i) (hjc : BelowF G C j)
    {P Q S T : Finset (Fin n)}
    (hiTop : OrientedTop C r i P Q true) (hjTop : OrientedTop C r j S T true)
    (hsQ : s ∈ Q) {e : Fin n} (heP : e ∈ P) (heS : e ∈ S) :
    ∀ c ∈ T, c = s := by
  classical
  have rawCross {k : ℕ} {R U : Finset (Fin n)} (hc : BelowF G C k)
      (ht : OrientedTop C r k R U true) {p q : Fin n}
      (hp : p ∈ R) (hq : q ∈ U) : G.Adj p q := by
    exact adjOfPair G (hc _ ((ht _ (originalEvalExcept h.1 r) (pairInput p q)).mpr
      ⟨Or.inl ⟨p,hp,by simp [pairInput]⟩, ⟨q,hq,by simp [pairInput]⟩⟩))
  have hes : G.Adj s e := (rawCross hic hiTop heP hsQ).symm
  have hev : e ≠ v := by
    intro he
    have ht : W (pairInput s v) (n+i) = true :=
      (hiTop W hW _).mpr
        ⟨Or.inl ⟨e,heP,by simp [pairInput,he]⟩, ⟨s,hsQ,by simp [pairInput]⟩⟩
    have ho := (collectorSemantics G C h hl hJ hW _).mpr ⟨i,hi,hia,hic,ht⟩
    rw [hmiss] at ho
    cases ho
  have hn : ∃ u ∈ A, ¬ G.Adj u v := by
    by_contra! hall
    obtain ⟨p,hp,q,hq,hpq⟩ := Finset.one_lt_card.mp hcardA
    exact hvd (commonNeighborUnique G h4 hpq (hstarB p hp).symm
      (hstarB q hq).symm (hall p hp) (hall q hq))
  obtain ⟨u,hu,huv⟩ := hn
  have sameColour (p q z : Fin n) (hp : colour p ≠ colour z)
      (hq : colour q ≠ colour z) : colour p = colour q := by
    generalize colour p = cp at hp ⊢
    generalize colour q = cq at hq ⊢
    generalize colour z = cz at hp hq
    cases cp <;> cases cq <;> cases cz <;> simp_all
  have hus : colour u = colour s :=
    sameColour u s d (hcolour u d (hstarB u hu).symm)
      (hcolour s d (hstarB s hs).symm)
  intro c hc
  have hce : G.Adj c e := (rawCross hjc hjTop heS hc).symm
  have hsc : colour s = colour c :=
    sameColour s c e (hcolour s e hes) (hcolour c e hce)
  have huc : colour u = colour c := hus.trans hsc
  let x : Fin n → Bool := fun z => decide (z = u ∨ z = v ∨ z = c)
  have hx : graphFun G ∅ x = true := hjc x
    ((hjTop _ (originalEvalExcept h.1 r) x).mpr
      ⟨Or.inr ⟨rfl,(hprod x).mpr
        ⟨⟨u,hu,by simp [x]⟩,⟨v,hv,by simp [x]⟩⟩⟩,⟨c,hc,by simp [x]⟩⟩)
  obtain ⟨p,q,hpq,hp,hq⟩ := (graph_true G x).mp hx
  have hp' : p = u ∨ p = v ∨ p = c := by simpa [x] using hp
  have hq' : q = u ∨ q = v ∨ q = c := by simpa [x] using hq
  have hcv : G.Adj c v := by
    rcases hp' with hp' | hp' | hp' <;> rcases hq' with hq' | hq' | hq' <;>
      rw [hp', hq'] at hpq
    · exact (G.ne_of_adj hpq rfl).elim
    · exact (huv hpq).elim
    · exact (hcolour u c hpq huc).elim
    · exact (huv hpq.symm).elim
    · exact (G.ne_of_adj hpq rfl).elim
    · exact hpq.symm
    · exact (hcolour c u hpq huc.symm).elim
    · exact hpq
    · exact (G.ne_of_adj hpq rfl).elim
  by_contra hcs
  exact hev (commonNeighborUnique G h4 (Ne.symm hcs) (hstarA v hv) hcv hes hce)


theorem indispensableCarrierOppositeSingleton {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    (h4 : NoFourCycle G) (colour : Fin n → Bool)
    (hcolour : ∀ u v, G.Adj u v → colour u ≠ colour v)
    {r a b : ℕ} (hJ : junk G C = {r}) (hab : (gateAt C r).inputs = [a,b])
    {A B : Finset (Fin n)} (hA : RawForm C r a A false)
    (hB : RawForm C r b B false) (hcardA : 1 < A.card)
    {s d v : Fin n} (hs : s ∈ A) (hv : v ∈ B) (hvd : v ≠ d)
    (hstarA : ∀ z ∈ B, G.Adj s z) (hstarB : ∀ z ∈ A, G.Adj d z)
    {W : (Fin n → Bool) → ℕ → Bool} (hW : EvalExcept n C r W)
    (hmiss : W (pairInput s v) C.output = false)
    {i j : ℕ} (hi : i < C.gates.length) (hia : (gateAt C i).op = GateOp.and)
    (hic : BelowF G C i) (hjc : BelowF G C j)
    {P Q S T : Finset (Fin n)}
    (hiTop : OrientedTop C r i P Q true) (hjTop : OrientedTop C r j S T true)
    (hsQ : s ∈ Q) {e : Fin n} (heP : e ∈ P) (heS : e ∈ S) :
    ∀ c ∈ T, c = s := by
  obtain ⟨hr, hand, _⟩ := junkMember G C hJ
  exact indispensableCarrierOppositeSingletonOfProduct G C h hl h4 colour hcolour hJ
    (originalJunkProduct h.1 hr hand hab hA hB) hcardA hs hv hvd hstarA hstarB
    hW hmiss hi hia hic hjc hiTop hjTop hsQ heP heS

#print axioms indispensableCarrierOppositeSingleton


/-- An actual directed OR route from an immediate reader of the unique
    junk to a wire; the junk itself is not an intermediate OR. -/
inductive OrCarrierRoute (n : ℕ) (C : Circuit) (r i : ℕ) : ℕ → Prop
  | direct (hi : i < C.gates.length) (hor : (gateAt C i).op = GateOp.or)
      (hread : n+r ∈ (gateAt C i).inputs) : OrCarrierRoute n C r i (n+i)
  | extend {w j : ℕ} (path : OrCarrierRoute n C r i w)
      (hj : j < C.gates.length) (hjr : j ≠ r)
      (hor : (gateAt C j).op = GateOp.or) (hm : w ∈ (gateAt C j).inputs) :
      OrCarrierRoute n C r i (n+j)

theorem carrierRouteFires {n : ℕ} {C : Circuit} {r i w : ℕ}
    (path : OrCarrierRoute n C r i w)
    {V : (Fin n → Bool) → ℕ → Bool} (hV : EvalExcept n C r V)
    (x : Fin n → Bool) (ht : V x (n+i) = true) : V x w = true := by
  induction path with
  | direct _ _ _ => exact ht
  | extend path hj hjr hor hm ih =>
    exact (evalExcept_or hV hj hjr hor x).mpr ⟨_,hm,ih⟩

/-- An immediate OR reader has a real raw leaf under false suspension.
    Absorption by a second junk-containing operand would contradict
    leastness; a pure other operand is nonzero. -/
theorem immediateOrReaderRawLeaf {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    {r i : ℕ} (hJ : junk G C = {r}) (hi : i < C.gates.length)
    (hor : (gateAt C i).op = GateOp.or) (hread : n+r ∈ (gateAt C i).inputs)
    {W : (Fin n → Bool) → ℕ → Bool} (hW : EvalExcept n C r W) :
    ∃ e : Fin n, W (pairInput e e) (n+i) = true := by
  have hri : r < i := Nat.lt_of_add_lt_add_left (h.1.2.1 i hi _ hread)
  have hd : ¬ BelowF G C i := by
    intro hc
    exact (junkMember G C hJ).2.2 (cleanOrOperands G C h.1 hi hor hc hread)
  obtain ⟨p,q,hpq⟩ := twoOperands h.1 hi
  obtain ⟨w,hw⟩ : ∃ w, (gateAt C i).inputs = [n+r,w] ∨
      (gateAt C i).inputs = [w,n+r] := by
    rcases (show n+r = p ∨ n+r = q by simpa [hpq] using hread) with he | he
    · exact ⟨q,Or.inl (by simpa [he] using hpq)⟩
    · exact ⟨p,Or.inr (by simpa [he] using hpq)⟩
  have hwm : w ∈ (gateAt C i).inputs := by
    rcases hw with he | he <;> simp [he]
  have hwlt := h.1.2.1 i hi w hwm
  obtain ⟨S,f,hS⟩ := dirtyRawForm G C h hl hJ w (by omega)
    (fun hc => hd (cleanWireReader G C h hl hi hwm hc).2)
  let V := fun (x : Fin n → Bool) k => val C (List.ofFn x) k
  have hV : EvalExcept n C r V := originalEvalExcept h.1 r
  have hf : f = false := by
    cases hflag : f
    · rfl
    · exfalso
      apply noEqualEarlier G C h i w hi hwlt
      intro x
      apply Bool.eq_iff_iff.mpr
      change V x (n+i) = true ↔ V x w = true
      constructor
      · intro ht
        obtain ⟨z,hz,hzt⟩ := (evalExcept_or hV hi hri.ne.symm hor x).mp ht
        have he : z = n+r ∨ z = w := by
          rcases hw with he | he
          · simpa [he] using hz
          · simpa [he,or_comm] using hz
        rcases he with he | he
        · exact (hS.2 V hV x).mpr (Or.inr ⟨hflag,he ▸ hzt⟩)
        · exact he ▸ hzt
      · intro ht
        exact (evalExcept_or hV hi hri.ne.symm hor x).mpr ⟨w,hwm,ht⟩
  obtain ⟨e,he,_⟩ := ((hS.2 V hV (fun _ => true)).mp
    (allTrueWires h.1 w (by omega))).resolve_right (by simp [hf])
  exact ⟨e,(evalExcept_or hW hi hri.ne.symm hor _).mpr
    ⟨w,hwm,(hS.2 W hW _).mpr (Or.inl ⟨e,he,by simp [pairInput]⟩)⟩⟩

/-- Every dirty non-junk wire that loses a true value traces to an
    actual immediate OR reader, rather than a merely semantic flag. -/
theorem lostDirtyWireRoute {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    {r : ℕ} (hJ : junk G C = {r})
    {V W : (Fin n → Bool) → ℕ → Bool} (hV : EvalExcept n C r V)
    (hW : EvalExcept n C r W) (x : Fin n → Bool) :
    ∀ w < n+C.gates.length, w ≠ n+r → ¬ CleanWire G C w →
      V x w = true → W x w = false →
      ∃ i < C.gates.length, (gateAt C i).op = GateOp.or ∧
        n+r ∈ (gateAt C i).inputs ∧ OrCarrierRoute n C r i w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hne hd hvt hwf
    by_cases hn : w < n
    · let v : Fin n := ⟨w,hn⟩
      have he : V x w = W x w := (hV.1 x v).trans (hW.1 x v).symm
      rw [hvt,hwf] at he
      cases he
    obtain ⟨j,rfl⟩ : ∃ j, w = n+j := ⟨w-n,by omega⟩
    have hj : j < C.gates.length := by omega
    have hjr : j ≠ r := by omega
    have hor : (gateAt C j).op = GateOp.or := by
      rcases h.1.1 _ (gateAt_mem hj) with hand | hor
      · exact (hjr (uniqueDirtyAnd G C hJ hj hd hand)).elim
      · exact hor
    obtain ⟨p,hp,hpv⟩ := (evalExcept_or hV hj hjr hor x).mp hvt
    have hpw : W x p = false := by
      cases he : W x p
      · rfl
      · have ht := (evalExcept_or hW hj hjr hor x).mpr ⟨p,hp,he⟩
        rw [hwf] at ht
        cases ht
    have hpl := h.1.2.1 j hj p hp
    by_cases he : p = n+r
    · have hm : n+r ∈ (gateAt C j).inputs := he ▸ hp
      exact ⟨j,hj,hor,hm,.direct hj hor hm⟩
    · obtain ⟨i,hi,hio,hir,path⟩ := ih p hpl (by omega) he
        (fun hc => hd (cleanWireReader G C h hl hj hp hc).2) hpv hpw
      exact ⟨i,hi,hio,hir,.extend path hj hjr hor hp⟩

/-- Shared topology supplies the common raw leaf required by the
    indispensable-carrier geometry. -/
theorem carrierRoutesShareRawLeaf {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    {r i p q : ℕ} (hJ : junk G C = {r}) (hi : i < C.gates.length)
    (hor : (gateAt C i).op = GateOp.or) (hir : n+r ∈ (gateAt C i).inputs)
    (hp : OrCarrierRoute n C r i p) (hq : OrCarrierRoute n C r i q)
    {P Q : Finset (Fin n)} {f g : Bool} (hP : RawForm C r p P f) (hQ : RawForm C r q Q g) :
    ∃ e : Fin n, e ∈ P ∧ e ∈ Q := by
  obtain ⟨W,hW,hzero⟩ := existsEvalExceptWithJunk C h.1 r (fun _ => false)
  obtain ⟨e,he⟩ := immediateOrReaderRawLeaf G C h hl hJ hi hor hir hW
  have member {w : ℕ} {S : Finset (Fin n)} {b : Bool}
      (path : OrCarrierRoute n C r i w) (hS : RawForm C r w S b) : e ∈ S := by
    obtain ⟨v,hv,hvx⟩ := ((hS.2 W hW _).mp
      (carrierRouteFires path hW (pairInput e e) he)).resolve_right (by simp [hzero])
    have heq : v = e := by simpa [pairInput] using hvx
    exact heq ▸ hv
  exact ⟨e,member hp hP,member hq hQ⟩

#print axioms carrierRouteFires
#print axioms immediateOrReaderRawLeaf
#print axioms lostDirtyWireRoute
#print axioms carrierRoutesShareRawLeaf


/-- A lost positive input identifies a concrete top and a concrete OR
    route to its junk-dependent operand. The opposite operand is pure.
    Direct AND readers are excluded by the already checked bridge. -/
theorem lostRoutedTop {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    {r : ℕ} (hJ : junk G C = {r})
    (hno : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      n+r ∉ (gateAt C j).inputs)
    {W : (Fin n → Bool) → ℕ → Bool} (hW : EvalExcept n C r W)
    (x : Fin n → Bool) (hx : graphFun G ∅ x = true) (hm : W x C.output = false) :
    ∃ i j p q : ℕ, ∃ S T : Finset (Fin n),
      i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧ n+r ∈ (gateAt C i).inputs ∧
      j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧ BelowF G C j ∧
      ((gateAt C j).inputs = [p,q] ∨ (gateAt C j).inputs = [q,p]) ∧
      RawForm C r p S true ∧ RawForm C r q T false ∧
      OrCarrierRoute n C r i p ∧ hits T x := by
  let V := fun (y : Fin n → Bool) w => val C (List.ofFn y) w
  have hV : EvalExcept n C r V := originalEvalExcept h.1 r
  have ho : V x C.output = true := (congrFun h.2.1 x).trans hx
  obtain ⟨j,hj,hja,hjc,hjv⟩ := (collectorSemantics G C h hl hJ hV x).mp ho
  have hjw : W x (n+j) = false := by
    cases he : W x (n+j)
    · rfl
    · have ht := (collectorSemantics G C h hl hJ hW x).mpr ⟨j,hj,hja,hjc,he⟩
      rw [hm] at ht
      cases ht
  obtain ⟨a,b,A,B,f,g,hab,hA,hB,hfg⟩ := topProduct G C h hl hJ hj hja hjc
  have orient {p q : ℕ} {S T : Finset (Fin n)} {k : Bool}
      (hpq : (gateAt C j).inputs = [p,q] ∨ (gateAt C j).inputs = [q,p])
      (hP : RawForm C r p S k) (hQ : RawForm C r q T false) :
      ∃ i : ℕ, i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧
        n+r ∈ (gateAt C i).inputs ∧ RawForm C r p S true ∧
        OrCarrierRoute n C r i p ∧ hits T x := by
    have ht (U : (Fin n → Bool) → ℕ → Bool) (hU : EvalExcept n C r U) :
        U x (n+j) = true ↔ U x p = true ∧ U x q = true := by
      rcases hpq with he | he
      · exact evalExcept_and hU hj (cleanDifferent G C hJ hjc) hja he x
      · rw [evalExcept_and hU hj (cleanDifferent G C hJ hjc) hja he x]
        exact and_comm
    obtain ⟨hpv,hqv⟩ := (ht V hV).mp hjv
    have hT : hits T x := by simpa [hits] using (hQ.2 V hV x).mp hqv
    have hqw : W x q = true := (hQ.2 W hW x).mpr (Or.inl hT)
    have hpw : W x p = false := by
      cases he : W x p
      · rfl
      · have htw := (ht W hW).mpr ⟨he,hqw⟩
        rw [hjw] at htw
        cases htw
    have hp : p ∈ (gateAt C j).inputs := by
      rcases hpq with he | he <;> simp [he]
    have hne : p ≠ n+r := fun he => hno j hj hja (he ▸ hp)
    have hpl := h.1.2.1 j hj p hp
    have hk := (rawFormLost hP hV hW x hpv hpw).1
    obtain ⟨i,hi,hio,hir,path⟩ := lostDirtyWireRoute G C h hl hJ hV hW x p
      (by omega) hne (noCleanAndOperand G C h j p hj hp hja) hpv hpw
    exact ⟨i,hi,hio,hir,hk ▸ hP,path,hT⟩
  rcases hfg with hf | hg
  · obtain ⟨i,hi,hio,hir,hB',hp,hT⟩ := orient (Or.inr hab) hB (hf ▸ hA)
    exact ⟨i,j,b,a,B,A,hi,hio,hir,hj,hja,hjc,Or.inr hab,hB',hf ▸ hA,hp,hT⟩
  · obtain ⟨i,hi,hio,hir,hA',hp,hT⟩ := orient (Or.inl hab) hA (hg ▸ hB)
    exact ⟨i,j,a,b,A,B,hi,hio,hir,hj,hja,hjc,Or.inl hab,hA',hg ▸ hB,hp,hT⟩

private lemma routedTopSemantics {n : ℕ} {C : Circuit} {r j p q : ℕ}
    (hj : j < C.gates.length) (hjr : j ≠ r) (hja : (gateAt C j).op = GateOp.and)
    (hpq : (gateAt C j).inputs = [p,q] ∨ (gateAt C j).inputs = [q,p])
    {S T : Finset (Fin n)} (hS : RawForm C r p S true) (hT : RawForm C r q T false) :
    OrientedTop C r j S T true := by
  intro V hV x
  rcases hpq with he | he
  · rw [evalExcept_and hV hj hjr hja he x,hS.2 V hV x,hT.2 V hV x]
    simp [hits]
  · rw [evalExcept_and hV hj hjr hja he x,hS.2 V hV x,hT.2 V hV x]
    simp [hits,and_comm]

/-- The missing noncentral edge s-v pins an actual immediate OR reader.
    Every clean top on this reader's route has opposite support {s}
    (the subset conclusion suffices; nonemptiness is automatic for pure
    operands in a constant-free AO circuit). The proof is symmetric in
    the two junk supports because only their product semantics is used. -/
theorem indispensableCarrierClass {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    (h4 : NoFourCycle G) (colour : Fin n → Bool)
    (hcolour : ∀ u v, G.Adj u v → colour u ≠ colour v)
    {r : ℕ} (hJ : junk G C = {r})
    (hno : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      n+r ∉ (gateAt C j).inputs)
    {A B : Finset (Fin n)}
    (hprod : ∀ x : Fin n → Bool, val C (List.ofFn x) (n+r) = true ↔ hits A x ∧ hits B x)
    (hcardA : 1 < A.card)
    {s d v : Fin n} (hs : s ∈ A) (hv : v ∈ B) (hvd : v ≠ d)
    (hstarA : ∀ z ∈ B, G.Adj s z) (hstarB : ∀ z ∈ A, G.Adj d z)
    {W : (Fin n → Bool) → ℕ → Bool} (hW : EvalExcept n C r W)
    (hmiss : W (pairInput s v) C.output = false) :
    ∃ i < C.gates.length, (gateAt C i).op = GateOp.or ∧ n+r ∈ (gateAt C i).inputs ∧
      (∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧ BelowF G C j ∧
        ∃ (p q : ℕ) (S T : Finset (Fin n)),
          ((gateAt C j).inputs = [p,q] ∨ (gateAt C j).inputs = [q,p]) ∧
          RawForm C r p S true ∧ RawForm C r q T false ∧ OrCarrierRoute n C r i p ∧ s ∈ T) ∧
      ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → BelowF G C j →
        ∀ (p q : ℕ) (S T : Finset (Fin n)),
          ((gateAt C j).inputs = [p,q] ∨ (gateAt C j).inputs = [q,p]) →
          RawForm C r p S true → RawForm C r q T false → OrCarrierRoute n C r i p →
          ∀ c ∈ T, c = s := by
  obtain ⟨i,j,p,q,S,T,hi,hio,hir,hj,hja,hjc,hpq,hS,hT,path,hitsT⟩ :=
    lostRoutedTop G C h hl hJ hno hW (pairInput s v) (pair_true G s v (hstarA v hv)) hmiss
  have ht := routedTopSemantics hj (cleanDifferent G C hJ hjc) hja hpq hS hT
  have hvT : v ∉ T := by
    intro hvt
    obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp hcardA
    have hcross (z) (hz : z ∈ A) : G.Adj z v :=
      carrierCross G h.1 hprod hjc ht hz hv hvt (Or.inl rfl) (Or.inr rfl)
    exact hvd (commonNeighborUnique G h4 hab (hstarB a ha).symm (hstarB b hb).symm
      (hcross a ha) (hcross b hb))
  have hsT : s ∈ T := by
    obtain ⟨z,hz,hzx⟩ := hitsT
    rcases (show z = s ∨ z = v by simpa [pairInput] using hzx) with he | he
    · exact he ▸ hz
    · exact (hvT (he ▸ hz)).elim
  refine ⟨i,hi,hio,hir,⟨j,hj,hja,hjc,p,q,S,T,hpq,hS,hT,path,hsT⟩,?_⟩
  intro k hk hka hkc u w P Q huw hP hQ path'
  obtain ⟨e,heS,heP⟩ := carrierRoutesShareRawLeaf G C h hl hJ hi hio hir path path' hS hP
  exact indispensableCarrierOppositeSingletonOfProduct G C h hl h4 colour hcolour hJ
    hprod hcardA hs hv hvd hstarA hstarB hW hmiss hj hja hjc hkc ht
    (routedTopSemantics hk (cleanDifferent G C hJ hkc) hka huw hP hQ) hsT heS heP

#print axioms lostRoutedTop
#print axioms indispensableCarrierClass


/-- Site-specific erasure: every read of the deleted gate receives its
    own earlier wire. No gate is added. -/
private def siteBypass (n : ℕ) (C : Circuit) (r : ℕ) (ρ : ℕ → ℕ) : Circuit :=
  ⟨(List.range (C.gates.length-1)).map (fun k =>
      if k < r then gateAt C k else aliasGate (n+r) (ρ (k+1)) (gateAt C (k+1))),
    aliasWire (n+r) 0 C.output⟩

private lemma siteBypassLength (n : ℕ) (C : Circuit) (r : ℕ) (ρ : ℕ → ℕ) :
    (siteBypass n C r ρ).gates.length = C.gates.length-1 := by simp [siteBypass]

private lemma siteBypassGate {n : ℕ} {C : Circuit} {r k : ℕ} {ρ : ℕ → ℕ}
    (hk : k < C.gates.length-1) :
    gateAt (siteBypass n C r ρ) k =
      if k < r then gateAt C k else aliasGate (n+r) (ρ (k+1)) (gateAt C (k+1)) := by
  have hk' : k < (siteBypass n C r ρ).gates.length := by rw [siteBypassLength]; exact hk
  rw [gateAt_eq hk']
  simp [siteBypass]

private lemma siteBypassAO {n : ℕ} {C : Circuit} (h : IsAO2 n C)
    {r : ℕ} {ρ : ℕ → ℕ} (hρ : ∀ j, ρ j < n+r) :
    IsAO2 n (siteBypass n C r ρ) := by
  have memGate (g : Gate) (hg : g ∈ (siteBypass n C r ρ).gates) :
      ∃ g' ∈ C.gates, g.op = g'.op ∧ g.inputs.length = g'.inputs.length := by
    simp only [siteBypass,List.mem_map,List.mem_range] at hg
    obtain ⟨k,hk,rfl⟩ := hg
    split_ifs with he
    · exact ⟨gateAt C k,gateAt_mem (by omega),rfl,rfl⟩
    · exact ⟨gateAt C (k+1),gateAt_mem (by omega),rfl,by simp [aliasGate]⟩
  refine ⟨?_,?_,?_⟩
  · intro g hg
    obtain ⟨g',hg',he,_⟩ := memGate g hg
    rw [he]
    exact h.1 g' hg'
  · intro k hk w hw
    rw [siteBypassLength] at hk
    rw [siteBypassGate hk] at hw
    split_ifs at hw with he
    · exact h.2.1 k (by omega) w hw
    · simp only [aliasGate,List.mem_map] at hw
      obtain ⟨u,hu,rfl⟩ := hw
      have hlt := h.2.1 (k+1) (by omega) u hu
      exact aliasWire_lt (hρ (k+1)) (by omega) (by omega)
  · intro g hg
    obtain ⟨g',hg',_,he⟩ := memGate g hg
    rw [he]
    exact h.2.2 g' hg'

private lemma siteBypassBefore {n : ℕ} {C : Circuit} {r : ℕ} {ρ : ℕ → ℕ}
    (hr : r < C.gates.length) (x : Fin n → Bool) :
    ∀ w < n+r, val (siteBypass n C r ρ) (List.ofFn x) w = val C (List.ofFn x) w := by
  apply val_prefix (n := n) (by simp) (by omega) (by rw [siteBypassLength]; omega)
  intro k hk
  rw [siteBypassGate (by omega),ite_eq_left hk]

private abbrev SiteVal {n : ℕ} (C : Circuit) (r : ℕ) (ρ : ℕ → ℕ) :=
  fun (x : Fin n → Bool) w => val (siteBypass n C r ρ) (List.ofFn x) (aliasWire (n+r) 0 w)

private lemma siteValRaw {n : ℕ} {C : Circuit} (h : IsAO2 n C)
    {r : ℕ} {ρ : ℕ → ℕ} (hr : r < C.gates.length) (x : Fin n → Bool) (v : Fin n) :
    SiteVal C r ρ x v.val = x v := by
  change val (siteBypass n C r ρ) (List.ofFn x) (aliasWire (n+r) 0 v.val) = x v
  rw [aliasWire_lt_self (by omega : v.val < n+r),siteBypassBefore hr x v.val (by omega)]
  exact (originalEvalExcept h r).1 x v

private lemma siteValGate {n : ℕ} {C : Circuit} (h : IsAO2 n C)
    {r : ℕ} {ρ : ℕ → ℕ} (hr : r < C.gates.length) (hρ : ∀ j, ρ j < n+r)
    (x : Fin n → Bool) {j : ℕ} (hj : j < C.gates.length) (hjr : j ≠ r) :
    SiteVal C r ρ x (n+j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun w =>
      if w = n+r then val C (List.ofFn x) (ρ j) else SiteVal C r ρ x w) := by
  dsimp only [SiteVal]
  by_cases hlt : j < r
  · rw [aliasWire_lt_self (by omega : n+j < n+r),siteBypassBefore hr x (n+j) (by omega)]
    have heq := (originalEvalExcept h r).2 x j hj hjr
    dsimp only at heq
    rw [heq]
    congr 1
    apply List.map_congr_left
    intro w hw
    have hwb := h.2.1 j hj w hw
    rw [ite_eq_right (by omega : w ≠ n+r),aliasWire_lt_self (by omega : w < n+r),
      siteBypassBefore hr x w (by omega)]
  · obtain ⟨k,rfl⟩ : ∃ k, j = k+1 := ⟨j-1,by omega⟩
    have hk : k < C.gates.length-1 := by omega
    have hkD : k < (siteBypass n C r ρ).gates.length := by rw [siteBypassLength]; exact hk
    rw [aliasWire_gt_self (by omega : n+r < n+(k+1)),
      show n+(k+1)-1 = n+k by omega,val_gate (n := n) (by simp) hkD,
      siteBypassGate hk,ite_eq_right (by omega : ¬ k < r)]
    simp only [aliasGate,List.map_map]
    congr 1
    apply List.map_congr_left
    intro w hw
    have hwb := h.2.1 (k+1) hj w hw
    have hren := aliasWire_lt (hρ (k+1)) (by omega : n+r ≤ n+k)
      (by omega : w < n+k+1)
    simp only [Function.comp_apply]
    rw [ite_eq_left hren]
    by_cases he : w = n+r
    · rw [ite_eq_left he,he,aliasWire_self,siteBypassBefore hr x _ (hρ _)]
    · rw [ite_eq_right he]
      congr 1
      by_cases hwlt : w < n+r
      · rw [aliasWire_lt_self hwlt,aliasWire_lt_self hwlt]
      · rw [aliasWire_gt_self (by omega : n+r < w),aliasWire_gt_self (by omega : n+r < w)]

private lemma routeReadSite {n : ℕ} {C : Circuit} {r i w : ℕ}
    (p : OrCarrierRoute n C r i w) :
    i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧ n+r ∈ (gateAt C i).inputs := by
  induction p with
  | direct hi ho hm => exact ⟨hi,ho,hm⟩
  | extend _ _ _ _ _ ih => exact ih

private lemma routeAfterHole {n : ℕ} {C : Circuit} (h : IsAO2 n C)
    {r i w : ℕ} (p : OrCarrierRoute n C r i w) : n+r < w := by
  induction p with
  | direct hi _ hm => exact h.2.1 i hi _ hm
  | extend _ hj _ _ hm ih => exact ih.trans (h.2.1 _ hj _ hm)

private lemma routeFlag {n : ℕ} {C : Circuit} (h : IsAO2 n C)
    {r i w : ℕ} (path : OrCarrierRoute n C r i w)
    {S : Finset (Fin n)} {f : Bool} (hS : RawForm C r w S f) : f = true := by
  obtain ⟨V,hV,hfill⟩ := existsEvalExceptWithJunk C h r (fun _ => true)
  obtain ⟨hi,hor,hm⟩ := routeReadSite path
  have hri : i ≠ r := by have := h.2.1 i hi _ hm; omega
  let x : Fin n → Bool := fun _ => false
  have ht := carrierRouteFires path hV x
    ((evalExcept_or hV hi hri hor x).mpr ⟨n+r,hm,hfill x⟩)
  simpa [x,hfill] using (hS.2 V hV x).mp ht

private lemma routeExistsOfFlag {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    {r w : ℕ} (hJ : junk G C = {r}) (hw : w < n+C.gates.length)
    (hne : w ≠ n+r) (hd : ¬ CleanWire G C w)
    {S : Finset (Fin n)} (hS : RawForm C r w S true) :
    ∃ i, OrCarrierRoute n C r i w := by
  obtain ⟨V,hV,htrue⟩ := existsEvalExceptWithJunk C h.1 r (fun _ => true)
  obtain ⟨W,hW,hfalse⟩ := existsEvalExceptWithJunk C h.1 r (fun _ => false)
  let x : Fin n → Bool := fun _ => false
  have hv : V x w = true := (hS.2 V hV x).mpr (Or.inr ⟨rfl,htrue x⟩)
  have hf : W x w = false := by
    cases he : W x w
    · rfl
    · have ht := (hS.2 W hW x).mp he
      simp [x,hfalse] at ht
  obtain ⟨i,_,_,_,hp⟩ := lostDirtyWireRoute G C h hl hJ hV hW x w hw hne hd hv hf
  exact ⟨i,hp⟩

private lemma siteRouteFires {n : ℕ} {C : Circuit} (h : IsAO2 n C)
    {r i w : ℕ} {ρ : ℕ → ℕ} (hr : r < C.gates.length) (hρ : ∀ j, ρ j < n+r)
    (x : Fin n → Bool) (path : OrCarrierRoute n C r i w)
    (hf : val C (List.ofFn x) (ρ i) = true) : SiteVal C r ρ x w = true := by
  induction path with
  | direct hi ho hm =>
    have hir : i ≠ r := by have := h.2.1 i hi _ hm; omega
    rw [siteValGate h hr hρ x hi hir,ho]
    simp only [GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
    exact ⟨n+r,hm,by simpa using hf⟩
  | @extend w j path hj hjr ho hm ih =>
    rw [siteValGate h hr hρ x hj hjr,ho]
    simp only [GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
    exact ⟨w,hm,by rw [ite_eq_right (Nat.ne_of_gt (routeAfterHole h path))]; exact ih⟩

/-- Dirty wires after a site-specific erasure retain the raw part
    of their false suspension and receive exactly the OR-route fills. -/
private theorem siteDirtySemantics {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    {r : ℕ} (hJ : junk G C = {r}) (ρ : ℕ → ℕ) (hρ : ∀ j, ρ j < n+r)
    {W : (Fin n → Bool) → ℕ → Bool} (hW : EvalExcept n C r W)
    (hzero : ∀ x, W x (n+r) = false) (x : Fin n → Bool) :
    ∀ w < n+C.gates.length, w ≠ n+r → ¬ CleanWire G C w →
      (SiteVal C r ρ x w = true ↔ W x w = true ∨
        ∃ i, OrCarrierRoute n C r i w ∧ val C (List.ofFn x) (ρ i) = true) := by
  have hr := (junkMember G C hJ).1
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hne hd
    by_cases hn : w < n
    · let v : Fin n := ⟨w,hn⟩
      have he : SiteVal C r ρ x w = W x w :=
        (siteValRaw h.1 hr x v).trans (hW.1 x v).symm
      rw [he]
      constructor
      · exact Or.inl
      · rintro (ht | ⟨i,path,_⟩)
        · exact ht
        · have := routeAfterHole h.1 path
          omega
    obtain ⟨j,rfl⟩ : ∃ j, w = n+j := ⟨w-n,by omega⟩
    have hj : j < C.gates.length := by omega
    have hjr : j ≠ r := by omega
    have hor : (gateAt C j).op = GateOp.or := by
      rcases h.1.1 _ (gateAt_mem hj) with hand | hor
      · exact (hjr (uniqueDirtyAnd G C hJ hj hd hand)).elim
      · exact hor
    rw [siteValGate h.1 hr hρ x hj hjr,hor]
    simp only [GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
    constructor
    · rintro ⟨p,hp,hpt⟩
      by_cases he : p = n+r
      · exact Or.inr ⟨j,.direct hj hor (he ▸ hp),by simpa [he] using hpt⟩
      · rw [ite_eq_right he] at hpt
        have hp' := h.1.2.1 j hj p hp
        rcases (ih p hp' (by omega) he
          (fun hc => hd (cleanWireReader G C h hl hj hp hc).2)).mp hpt with ht | ⟨i,path,hfill⟩
        · exact Or.inl ((evalExcept_or hW hj hjr hor x).mpr ⟨p,hp,ht⟩)
        · exact Or.inr ⟨i,.extend path hj hjr hor hp,hfill⟩
    · rintro (ht | ⟨i,path,hfill⟩)
      · obtain ⟨p,hp,hpt⟩ := (evalExcept_or hW hj hjr hor x).mp ht
        have he : p ≠ n+r := by
          intro he
          rw [he,hzero] at hpt
          cases hpt
        refine ⟨p,hp,?_⟩
        rw [ite_eq_right he]
        have hpl := h.1.2.1 j hj p hp
        exact (ih p hpl (by omega) he
          (fun hc => hd (cleanWireReader G C h hl hj hp hc).2)).mpr (Or.inl hpt)
      · have hv := siteRouteFires h.1 hr hρ x path hfill
        rw [siteValGate h.1 hr hρ x hj hjr,hor] at hv
        simpa only [GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq] using hv

/-- A clean OR collector uses only clean equations. Site-specific
    redirection cannot change any of those OR read sites. -/
private theorem siteCollector {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    {r : ℕ} (hJ : junk G C = {r}) (ρ : ℕ → ℕ) (hρ : ∀ j, ρ j < n+r)
    (x : Fin n → Bool) :
    SiteVal C r ρ x C.output = true ↔ ∃ j < C.gates.length,
      (gateAt C j).op = GateOp.and ∧ BelowF G C j ∧ SiteVal C r ρ x (n+j) = true := by
  have hr := (junkMember G C hJ).1
  have orEq (j) (hj : j < C.gates.length) (hor : (gateAt C j).op = GateOp.or)
      (hc : BelowF G C j) :
      SiteVal C r ρ x (n+j) = true ↔
        ∃ w ∈ (gateAt C j).inputs, SiteVal C r ρ x w = true := by
    have hno : n+r ∉ (gateAt C j).inputs :=
      fun hm => (junkMember G C hJ).2.2 (cleanOrOperands G C h.1 hj hor hc hm)
    rw [siteValGate h.1 hr hρ x hj (cleanDifferent G C hJ hc),hor]
    simp only [GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
    exact exists_congr (fun w => and_congr_right (fun hm => by
      have hne : w ≠ n+r := fun he => hno (he ▸ hm)
      rw [ite_eq_right hne]))
  have down : ∀ j < C.gates.length, BelowF G C j → SiteVal C r ρ x (n+j) = true →
      ∃ k < C.gates.length, (gateAt C k).op = GateOp.and ∧
        BelowF G C k ∧ SiteVal C r ρ x (n+k) = true := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj hc ht
      rcases h.1.1 _ (gateAt_mem hj) with ha | ho
      · exact ⟨j,hj,ha,hc,ht⟩
      · obtain ⟨w,hm,hw⟩ := (orEq j hj ho hc).mp ht
        have hcw := cleanOrOperands G C h.1 hj ho hc hm
        have hlt := h.1.2.1 j hj w hm
        by_cases hn : w < n
        · exact (rawNotClean G C ⟨w,hn⟩ hcw).elim
        · obtain ⟨k,rfl⟩ : ∃ k, w = n+k := ⟨w-n,by omega⟩
          exact ih k (by omega) (by omega) hcw hw
  have up : ∀ d : ℕ, ∀ j < C.gates.length, C.gates.length-j = d →
      BelowF G C j → SiteVal C r ρ x (n+j) = true → SiteVal C r ρ x C.output = true := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro j hj hd hc ht
      by_cases he : C.output = n+j
      · rwa [he]
      · obtain ⟨a,b,hab⟩ := twoOperands h.1 hj
        have ha := h.1.2.1 j hj a (by simp [hab])
        obtain ⟨k,hjk,hk,hm⟩ := noUnreadGate G C h j a hj ha he
        obtain ⟨hor,hck⟩ := cleanReader G C h hl hj hc (allLive G C h k hk) hm
        exact ih _ (by omega) k hk rfl hck ((orEq k hk hor hck).mpr ⟨n+j,hm,ht⟩)
  constructor
  · intro ht
    have ho := outputLast G C h (by omega : 0 < C.gates.length)
    have hc : BelowF G C (C.gates.length-1) := by
      intro y hy
      have he : C.eval (List.ofFn y) = graphFun G ∅ y := congrFun h.2.1 y
      rw [← he]
      change val C (List.ofFn y) C.output = true
      rwa [ho]
    rw [ho] at ht
    exact down _ (by omega) hc ht
  · rintro ⟨j,hj,_,hc,ht⟩
    exact up _ j hj rfl hc ht

/-- General strict site-bypass criterion. Safety is checked against
    each routed top's pure opposite support; completeness only requires
    fills on genuinely lost positive inputs. -/
theorem noOneJunkSiteReplacement {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    {r : ℕ} (hJ : junk G C = {r})
    (hno : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → n+r ∉ (gateAt C j).inputs)
    (ρ : ℕ → ℕ) (hρ : ∀ j, ρ j < n+r)
    {W : (Fin n → Bool) → ℕ → Bool} (hW : EvalExcept n C r W)
    (hzero : ∀ x, W x (n+r) = false)
    (hsafe : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → BelowF G C j →
      ∀ (p q : ℕ) (S T : Finset (Fin n)),
        ((gateAt C j).inputs = [p,q] ∨ (gateAt C j).inputs = [q,p]) →
        RawForm C r p S true → RawForm C r q T false →
        ∀ i, OrCarrierRoute n C r i p → ∀ x : Fin n → Bool,
          val C (List.ofFn x) (ρ i) = true → hits T x → graphFun G ∅ x = true)
    (hfill : ∀ u v, G.Adj u v → W (pairInput u v) C.output = false →
      ∀ i, OrCarrierRoute n C r i (n+i) → val C (List.ofFn (pairInput u v)) (ρ i) = true) :
    False := by
  have hr := (junkMember G C hJ).1
  let D := siteBypass n C r ρ
  let Z := SiteVal (n := n) C r ρ
  have hD : IsAO2 n D := siteBypassAO h.1 hρ
  have hlen : D.gates.length = C.gates.length-1 := siteBypassLength n C r ρ
  have hfun (x : Fin n → Bool) : circuitFun n D x = Z x C.output := rfl
  have topEq (x : Fin n → Bool) (j) (hj : j < C.gates.length)
      (ha : (gateAt C j).op = GateOp.and) (hc : BelowF G C j) {p q : ℕ}
      (hpq : (gateAt C j).inputs = [p,q] ∨ (gateAt C j).inputs = [q,p]) :
      Z x (n+j) = true ↔ Z x p = true ∧ Z x q = true := by
    have hp : p ∈ (gateAt C j).inputs := by rcases hpq with he | he <;> simp [he]
    have hq : q ∈ (gateAt C j).inputs := by rcases hpq with he | he <;> simp [he]
    have hnp : p ≠ n+r := fun he => hno j hj ha (he ▸ hp)
    have hnq : q ≠ n+r := fun he => hno j hj ha (he ▸ hq)
    change SiteVal C r ρ x (n+j) = true ↔ _
    rw [siteValGate h.1 hr hρ x hj (cleanDifferent G C hJ hc),ha]
    rcases hpq with he | he <;> simp [he,GateOp.eval,hnp,hnq,Z,and_comm]
  have wireEq (x : Fin n → Bool) (j) (hj : j < C.gates.length)
      (ha : (gateAt C j).op = GateOp.and) {p : ℕ} (hp : p ∈ (gateAt C j).inputs) :
      Z x p = true ↔ W x p = true ∨
        ∃ i, OrCarrierRoute n C r i p ∧ val C (List.ofFn x) (ρ i) = true :=
    siteDirtySemantics G C h hl hJ ρ hρ hW hzero x p
      ((h.1.2.1 j hj p hp).trans (Nat.add_lt_add_left hj n))
      (fun he => hno j hj ha (he ▸ hp)) (noCleanAndOperand G C h j p hj hp ha)
  have pure (x : Fin n → Bool) (j) (hj : j < C.gates.length)
      (ha : (gateAt C j).op = GateOp.and) {p : ℕ} (hp : p ∈ (gateAt C j).inputs)
      {S : Finset (Fin n)} (hS : RawForm C r p S false) :
      Z x p = true ↔ hits S x := by
    rw [wireEq x j hj ha hp]
    constructor
    · rintro (ht | ⟨i,path,_⟩)
      · simpa [hits] using (hS.2 W hW x).mp ht
      · cases routeFlag h.1 path hS
    · intro ht
      exact Or.inl ((hS.2 W hW x).mpr (Or.inl ht))
  have sound (x : Fin n → Bool) (hz : Z x C.output = true) : graphFun G ∅ x = true := by
    obtain ⟨j,hj,ha,hc,ht⟩ := (siteCollector G C h hl hJ ρ hρ x).mp hz
    obtain ⟨a,b,A,B,f,g,hab,hA,hB,hfg⟩ := topProduct G C h hl hJ hj ha hc
    have orient {p q : ℕ} {S T : Finset (Fin n)} {k : Bool}
        (hpq : (gateAt C j).inputs = [p,q] ∨ (gateAt C j).inputs = [q,p])
        (hS : RawForm C r p S k) (hT : RawForm C r q T false) : graphFun G ∅ x = true := by
      have hp : p ∈ (gateAt C j).inputs := by rcases hpq with he | he <;> simp [he]
      have hq : q ∈ (gateAt C j).inputs := by rcases hpq with he | he <;> simp [he]
      obtain ⟨hzp,hzq⟩ := (topEq x j hj ha hc hpq).mp ht
      have hTx := (pure x j hj ha hq hT).mp hzq
      rcases (wireEq x j hj ha hp).mp hzp with hwp | ⟨i,path,hv⟩
      · have hwq := (hT.2 W hW x).mpr (Or.inl hTx)
        have hwj : W x (n+j) = true := by
          rcases hpq with he | he
          · exact (evalExcept_and hW hj (cleanDifferent G C hJ hc) ha he x).mpr ⟨hwp,hwq⟩
          · exact (evalExcept_and hW hj (cleanDifferent G C hJ hc) ha he x).mpr ⟨hwq,hwp⟩
        exact suspendedFalseSound G C h hl hJ hW hzero x
          ((collectorSemantics G C h hl hJ hW x).mpr ⟨j,hj,ha,hc,hwj⟩)
      · exact hsafe j hj ha hc p q S T hpq (routeFlag h.1 path hS ▸ hS) hT i path x hv hTx
    rcases hfg with hf | hg
    · exact orient (Or.inr hab) hB (hf ▸ hA)
    · exact orient (Or.inl hab) hA (hg ▸ hB)
  have edge (u v : Fin n) (huv : G.Adj u v) : Z (pairInput u v) C.output = true := by
    let x := pairInput u v
    by_cases hw : W x C.output = true
    · obtain ⟨j,hj,ha,hc,ht⟩ := (collectorSemantics G C h hl hJ hW x).mp hw
      obtain ⟨p,q,hpq⟩ := twoOperands h.1 hj
      obtain ⟨hp,hq⟩ := (evalExcept_and hW hj (cleanDifferent G C hJ hc) ha hpq x).mp ht
      exact (siteCollector G C h hl hJ ρ hρ x).mpr ⟨j,hj,ha,hc,
        (topEq x j hj ha hc (Or.inl hpq)).mpr
          ⟨(wireEq x j hj ha (p := p) (by simp [hpq])).mpr (Or.inl hp),
           (wireEq x j hj ha (p := q) (by simp [hpq])).mpr (Or.inl hq)⟩⟩
    · have hf : W x C.output = false := by
        cases he : W x C.output
        · rfl
        · exact (hw he).elim
      obtain ⟨i,j,p,q,S,T,hi,hio,hir,hj,hja,hjc,hpq,hS,hT,path,hTx⟩ :=
        lostRoutedTop G C h hl hJ hno hW x (pair_true G u v huv) hf
      have hp : p ∈ (gateAt C j).inputs := by rcases hpq with he | he <;> simp [he]
      have hq : q ∈ (gateAt C j).inputs := by rcases hpq with he | he <;> simp [he]
      exact (siteCollector G C h hl hJ ρ hρ x).mpr ⟨j,hj,hja,hjc,
        (topEq x j hj hja hjc hpq).mpr
          ⟨(wireEq x j hj hja hp).mpr (Or.inr ⟨i,path,hfill u v huv hf i (.direct hi hio hir)⟩),
            (pure x j hj hja hq hT).mpr hTx⟩⟩
  have hcorrect : circuitFun n D = graphFun G ∅ := by
    funext x
    apply Bool.eq_iff_iff.mpr
    constructor
    · rw [hfun]
      exact sound x
    · intro hx
      obtain ⟨u,v,huv,hu,hv⟩ := (graph_true G x).mp hx
      apply circuit_monotone n D (ao_mono hD) (pairInput u v) x ?_ ((hfun _).trans (edge u v huv))
      intro z hz
      rcases (show z = u ∨ z = v by simpa [pairInput] using hz) with rfl | rfl
      · exact hu
      · exact hv
  have hm := h.2.2 D hD hcorrect
  change C.gates.length ≤ D.gates.length at hm
  omega

/-- Both indispensable stars with at most two readers force separate
    carrier classes. Replacing each read by the opposite junk provider
    preserves every edge and creates none, strictly erasing the junk. -/
theorem noTwoOrReadersBothStars {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    (h4 : NoFourCycle G) (colour : Fin n → Bool)
    (hcolour : ∀ u v, G.Adj u v → colour u ≠ colour v)
    {r a b : ℕ} (hJ : junk G C = {r}) (hab : (gateAt C r).inputs = [a,b])
    (hno : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → n+r ∉ (gateAt C j).inputs)
    (hcount : ((Finset.range C.gates.length).filter (fun j => n+r ∈ (gateAt C j).inputs)).card ≤ 2)
    {A B : Finset (Fin n)} (hA : RawForm C r a A false) (hB : RawForm C r b B false)
    (hcardA : 1 < A.card) (hcardB : 1 < B.card)
    {s d u v : Fin n} (hs : s ∈ A) (hd : d ∈ B) (hu : u ∈ A) (hv : v ∈ B)
    (hus : u ≠ s) (hvd : v ≠ d)
    (hstarA : ∀ z ∈ B, G.Adj s z) (hstarB : ∀ z ∈ A, G.Adj d z)
    {W : (Fin n → Bool) → ℕ → Bool} (hW : EvalExcept n C r W)
    (hzero : ∀ x, W x (n+r) = false)
    (hmissA : W (pairInput s v) C.output = false)
    (hmissB : W (pairInput u d) C.output = false) : False := by
  classical
  obtain ⟨hr,hand,_⟩ := junkMember G C hJ
  have hprod := originalJunkProduct h.1 hr hand hab hA hB
  have hprod' (x : Fin n → Bool) : val C (List.ofFn x) (n+r) = true ↔ hits B x ∧ hits A x :=
    (hprod x).trans and_comm
  obtain ⟨i,hi,hio,hir,wi,hclassI⟩ := indispensableCarrierClass G C h hl h4 colour hcolour hJ
    hno hprod hcardA hs hv hvd hstarA hstarB hW hmissA
  have hmissB' : W (pairInput d u) C.output = false := by simpa [pairInputComm] using hmissB
  obtain ⟨k,hk,hko,hkr,wk,hclassK⟩ := indispensableCarrierClass G C h hl h4 colour hcolour hJ
    hno hprod' hcardB hd hu hus hstarB hstarA hW hmissB'
  have hik : i ≠ k := by
    intro he
    obtain ⟨j,hj,hja,hjc,p,q,S,T,hpq,hS,hT,path,hsT⟩ := wi
    exact (G.ne_of_adj (hstarA d hd))
      (hclassK j hj hja hjc p q S T hpq hS hT (he ▸ path) s hsT)
  let R := (Finset.range C.gates.length).filter (fun j => n+r ∈ (gateAt C j).inputs)
  have classify (j) (hj : j < C.gates.length) (hm : n+r ∈ (gateAt C j).inputs) : j = i ∨ j = k := by
    by_contra hn
    have hni : j ≠ i := fun he => hn (Or.inl he)
    have hnk : j ≠ k := fun he => hn (Or.inr he)
    have hsub : ({i,k,j} : Finset ℕ) ⊆ R := by
      intro t ht
      rcases (show t = i ∨ t = k ∨ t = j by simpa using ht) with rfl | rfl | rfl <;>
        simp [R,Finset.mem_range, hi, hir, hk, hkr, hj, hm]
    have hle := Finset.card_le_card hsub
    have hthree : ({i,k,j} : Finset ℕ).card = 3 := by simp [hik,hni.symm,hnk.symm]
    rw [hthree] at hle
    change R.card ≤ 2 at hcount
    omega
  have hal := h.1.2.1 r hr a (by simp [hab])
  have hbl := h.1.2.1 r hr b (by simp [hab])
  let ρ := fun j => if j = i then b else a
  apply noOneJunkSiteReplacement G C h hl hJ hno ρ
    (fun j => by change (if j = i then b else a) < n+r; split_ifs <;> assumption) hW hzero
  · intro j hj hja hjc p q S T hpq hS hT t path x hf ht
    obtain ⟨htl,_,htm⟩ := routeReadSite path
    obtain ⟨z,hz,hzx⟩ := ht
    rcases classify t htl htm with he | he
    · have hzs := hclassI j hj hja hjc p q S T hpq hS hT (he ▸ path) z hz
      have hb : val C (List.ofFn x) b = true := by simpa [ρ,he] using hf
      obtain ⟨w,hw,hwx⟩ := ((hB.2 _ (originalEvalExcept h.1 r) x).mp hb).resolve_right (by simp)
      exact (graph_true G x).mpr ⟨s,w,hstarA w hw,hzs ▸ hzx,hwx⟩
    · have hzd := hclassK j hj hja hjc p q S T hpq hS hT (he ▸ path) z hz
      have ha : val C (List.ofFn x) a = true := by simpa [ρ,he,hik.symm] using hf
      obtain ⟨w,hw,hwx⟩ := ((hA.2 _ (originalEvalExcept h.1 r) x).mp ha).resolve_right (by simp)
      exact (graph_true G x).mpr ⟨d,w,hstarB w hw,hzd ▸ hzx,hwx⟩
  · intro u' v' huv hm t _
    let V := fun (x : Fin n → Bool) w => val C (List.ofFn x) w
    let x := pairInput u' v'
    have hV := originalEvalExcept h.1 r
    have ho : V x C.output = true := (congrFun h.2.1 x).trans (pair_true G u' v' huv)
    obtain ⟨j,hj,hja,hjc,hjv⟩ := (collectorSemantics G C h hl hJ hV x).mp ho
    obtain ⟨S,T,f,ht⟩ := orientedTop G C h hl hJ hj hja hjc
    obtain ⟨hp,hq⟩ := (ht V hV x).mp hjv
    have hjunk : V x (n+r) = true := by
      rcases hp with hp | hp
      · have hw := (collectorSemantics G C h hl hJ hW x).mpr
          ⟨j,hj,hja,hjc,(ht W hW x).mpr ⟨Or.inl hp,hq⟩⟩
        rw [hm] at hw
        cases hw
      · exact hp.2
    obtain ⟨ha,hb⟩ := (hprod x).mp hjunk
    have hva := (hA.2 V hV x).mpr (Or.inl ha)
    have hvb := (hB.2 V hV x).mpr (Or.inl hb)
    change V x (ρ t) = true
    change V x (if t = i then b else a) = true
    split_ifs <;> assumption

#print axioms noOneJunkSiteReplacement
#print axioms noTwoOrReadersBothStars


/-- Any lost positive input activates the original junk product. -/
private lemma lostPositiveJunk {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    {r : ℕ} (hJ : junk G C = {r})
    {W : (Fin n → Bool) → ℕ → Bool} (hW : EvalExcept n C r W)
    (x : Fin n → Bool) (hx : graphFun G ∅ x = true) (hm : W x C.output = false) :
    val C (List.ofFn x) (n+r) = true := by
  let V := fun (y : Fin n → Bool) w => val C (List.ofFn y) w
  have hV : EvalExcept n C r V := originalEvalExcept h.1 r
  have ho : V x C.output = true := (congrFun h.2.1 x).trans hx
  obtain ⟨j,hj,hja,hjc,hjv⟩ := (collectorSemantics G C h hl hJ hV x).mp ho
  obtain ⟨S,T,f,ht⟩ := orientedTop G C h hl hJ hj hja hjc
  obtain ⟨hp,hq⟩ := (ht V hV x).mp hjv
  rcases hp with hp | hp
  · have hw := (collectorSemantics G C h hl hJ hW x).mpr
      ⟨j,hj,hja,hjc,(ht W hW x).mpr ⟨Or.inl hp,hq⟩⟩
    rw [hm] at hw
    cases hw
  · exact hp.2

private lemma pairEqOfHits {n : ℕ} (u v p q : Fin n)
    (hp : pairInput u v p = true) (hq : pairInput u v q = true) (hne : p ≠ q) :
    pairInput u v = pairInput p q := by
  have hp' : p = u ∨ p = v := by simpa [pairInput] using hp
  have hq' : q = u ∨ q = v := by simpa [pairInput] using hq
  rcases hp' with hp' | hp' <;> rcases hq' with hq' | hq'
  · exact (hne (hp'.trans hq'.symm)).elim
  · simp [hp',hq']
  · simpa [hp',hq'] using pairInputComm u v
  · exact (hne (hp'.trans hq'.symm)).elim

private lemma memberOfPair {n : ℕ} {u v a b c : Fin n}
    (ha : a = u ∨ a = v) (hb : b = u ∨ b = v) (hc : c = u ∨ c = v)
    (hne : a ≠ b) : c = a ∨ c = b := by
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact (hne (ha.trans hb.symm)).elim
  · exact hc.imp (fun h => h.trans ha.symm) (fun h => h.trans hb.symm)
  · exact hc.symm.imp (fun h => h.trans ha.symm) (fun h => h.trans hb.symm)
  · exact (hne (ha.trans hb.symm)).elim

/-- A pre-junk provider outside the residual-use cone can pay for
    a one-star repair, while its disjoint other provider stays intact. -/
private theorem exclusiveProviderOneStar {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    {r i a b : ℕ} (hJ : junk G C = {r})
    (hi : i < C.gates.length) (hir : n+r ∈ (gateAt C i).inputs)
    (hal : a < n+r) (hbl : b < n+r) (hbd : ¬ CleanWire G C b)
    {A B : Finset (Fin n)} (hA : RawForm C r a A false) (hB : RawForm C r b B false)
    (hdisj : Disjoint A B) (hcardA : 1 < A.card)
    {s : Fin n} (hs : s ∈ A) (hstar : ∀ v ∈ B, G.Adj s v)
    (huse : ¬ ResidualUse G C r (suspendedValue (n := n) C r (fun _ => false) (fun _ => true)) a)
    (hcover : ∀ u v, G.Adj u v →
      suspendedValue (n := n) C r (fun _ => false) (pairInput u v) C.output = true ∨
      (pairInput u v s = true ∧ hits B (pairInput u v))) : False := by
  classical
  have hr := (junkMember G C hJ).1
  have hri : r < i := Nat.lt_of_add_lt_add_left (h.1.2.1 i hi _ hir)
  let W := suspendedValue (n := n) C r (fun _ => false)
  have hW : EvalExcept n C r W := suspendedValue_evalExcept C h.1 r _
  have hzero (x) : W x (n+r) = false := suspendedValue_hole C r _ x
  have hna : n ≤ a := by
    by_contra! hn
    let u : Fin n := ⟨a,hn⟩
    obtain ⟨v,hv,w,hw,hvw⟩ := Finset.one_lt_card.mp hcardA
    have ident (z : Fin n) (hz : z ∈ A) : u = z := by
      have ht := (hA.2 W hW (pairInput z z)).mpr (Or.inl ⟨z,hz,by simp [pairInput]⟩)
      simpa [pairInput] using (hW.1 (pairInput z z) u).symm.trans ht
    exact hvw ((ident v hv).symm.trans (ident w hw))
  obtain ⟨j,rfl⟩ : ∃ j, a = n+j := ⟨a-n,by omega⟩
  have hjr : j < r := by omega
  have hj := hjr.trans hr
  have hjs : W (pairInput s s) (n+j) = true :=
    (hA.2 W hW _).mpr (Or.inl ⟨s,hs,by simp [pairInput]⟩)
  have hbs : W (pairInput s s) b = false := by
    cases he : W (pairInput s s) b
    · rfl
    · obtain ⟨z,hz,hzx⟩ := ((hB.2 W hW _).mp he).resolve_right (by simp)
      have heq : z = s := by simpa [pairInput] using hzx
      exact (Finset.disjoint_left.mp hdisj hs (heq ▸ hz)).elim
  let M : ℕ → ℕ → Bool := fun k _ => decide (k = j)
  let Z := maskedValue (n := n) C r M (fun _ => false)
  have hZraw := maskedValue_raw C r M (fun _ : Fin n → Bool => false)
  have hZzero := maskedValue_hole C r M (fun _ : Fin n → Bool => false)
  have hZgate (x) (k) (hk : k < C.gates.length) (hkr : k ≠ r) :=
    maskedValue_gate C h.1 r M (fun _ : Fin n → Bool => false) x hk hkr
  have hZle (x) (w) (hw : w < n+C.gates.length) (ht : Z x w = true) : W x w = true :=
    maskedValueLe C h.1 r (fun _ _ => false) M (by simp) (fun _ => false) x w hw ht
  have hkeep : ∀ x, W x C.output = true → Z x C.output = true := by
    apply residualOutputPreserved G C h hl hJ hW hzero hZraw hZzero
    intro x k hk hkr hu
    have hkj : k ≠ j := by
      rintro rfl
      rcases hu with hc | hu
      · exact (rawNotClean G C s (fun x hx => hc x
          ((hA.2 _ (originalEvalExcept h.1 r) x).mpr (Or.inl ⟨s,hs,((originalEvalExcept h.1 r).1 x s).symm.trans hx⟩)))).elim
      · exact huse hu
    simpa [M,hkj] using hZgate x k hk hkr
  have hZB (x) : Z x b = W x b :=
    extraMaskPreservesProvider G C h hl hJ hW s hjs (fun _ _ => false) M
      (by intro k w hk; simp [M,hk]) (fun _ => false) x b hbl hbd hbs
  have hout := outputLast G C h (by omega : 0 < C.gates.length)
  have hob : C.output < n+C.gates.length := by omega
  have hbb : b < n+C.gates.length := by omega
  obtain ⟨D,hD,hlen,hwires⟩ := compileMaskedSuspension C h.1 M Z hZraw hZgate hZzero
    {r,i,j} (by
      intro k hk
      rcases (show k = r ∨ k = i ∨ k = j by simpa using hk) with rfl | rfl | rfl <;>
        exact Finset.mem_range.mpr (by assumption)) (by
      intro k hk
      rcases (show k = r ∨ k = i ∨ k = j by simpa using hk) with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr ⟨n+r,hir,Or.inr (hZzero _)⟩
      · obtain ⟨p,q,hpq⟩ := twoOperands h.1 hj
        exact Or.inr ⟨p,by simp [hpq],Or.inl (by simp [M])⟩)
  have hcard : ({r,i,j} : Finset ℕ).card = 3 := by
    have hji : j ≠ i := by omega
    simp [hri.ne,hjr.ne.symm,hji.symm]
  rw [hcard] at hlen
  let star : RepairStar n := ⟨s,B⟩
  have hprovider (x) : Z x b = star.provider x := by
    apply Bool.eq_iff_iff.mpr
    rw [hZB x]
    simpa [star,RepairStar.provider] using hB.2 W hW x
  have hp : WireAvailable D star.provider := (funext hprovider) ▸ hwires b hbb
  obtain ⟨E,hE,hcost,houtval,_⟩ :=
    appendRepairStar D hD (fun x => Z x C.output) (hwires C.output hob) star hp
  have hsmall : E.gates.length < C.gates.length := by
    cases ht : Z (fun _ => true) C.output <;> simp [ht] at hcost <;> omega
  have hpos (u v : Fin n) (huv : G.Adj u v) :
      (Z (pairInput u v) C.output || star.fires (pairInput u v)) = true := by
    rcases hcover u v huv with ho | ⟨hsx,hBhit⟩
    · simp [hkeep _ ho]
    · have ht : star.fires (pairInput u v) = true := by
        simpa [star,RepairStar.fires,RepairStar.provider,hits] using And.intro hsx hBhit
      simp [ht]
  rcases houtval with hfalse | ⟨o,_,heval⟩
  · have hnone (u v : Fin n) (huv : G.Adj u v) : False :=
      Bool.false_ne_true ((hfalse _).symm.trans (hpos u v huv))
    have := emptyGraphNoGates G C h hnone
    omega
  · let F : Circuit := ⟨E.gates,o⟩
    have hF : IsAO2 n F := hE
    have hfun (x : Fin n → Bool) : circuitFun n F x = (Z x C.output || star.fires x) := heval x
    have hcorrect : circuitFun n F = graphFun G ∅ := by
      funext x
      apply Bool.eq_iff_iff.mpr
      constructor
      · intro hx
        rw [hfun,Bool.or_eq_true] at hx
        rcases hx with ho | ht
        · exact suspendedFalseSound G C h hl hJ hW hzero x (hZle x C.output hob ho)
        · obtain ⟨hsx,z,hz,hzx⟩ : x s = true ∧ hits B x := by
            simpa [star,RepairStar.fires,RepairStar.provider,hits] using ht
          exact (graph_true G x).mpr ⟨s,z,hstar z hz,hsx,hzx⟩
      · intro hx
        obtain ⟨u,v,huv,hu,hv⟩ := (graph_true G x).mp hx
        apply circuit_monotone n F (ao_mono hF) (pairInput u v) x ?_ ((hfun _).trans (hpos u v huv))
        intro z hz
        rcases (show z = u ∨ z = v by simpa [pairInput] using hz) with rfl | rfl
        · exact hu
        · exact hv
    have hm := h.2.2 F hF hcorrect
    change C.gates.length ≤ E.gates.length at hm
    omega

set_option maxHeartbeats 1000000 in
/-- The sole carrier has a uniform opposite colour. Every missing
    edge therefore belongs to the seed centre's star. If the other
    provider is protected, its residual neighbour supplies the sole
    possible universal leaf, and the nonuniversal leaves give a safe
    replacement at the carrier. -/
private theorem noSoleOrReaderOfSeed {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    (h4 : NoFourCycle G) (colour : Fin n → Bool)
    (hcolour : ∀ u v, G.Adj u v → colour u ≠ colour v)
    {r i a b : ℕ} (hJ : junk G C = {r})
    (hno : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → n+r ∉ (gateAt C j).inputs)
    (hi : i < C.gates.length) (hio : (gateAt C i).op = GateOp.or)
    (hir : n+r ∈ (gateAt C i).inputs)
    (only : ∀ k < C.gates.length, n+r ∈ (gateAt C k).inputs → k = i)
    (hal : a < n+r) (hbl : b < n+r) (hbd : ¬ CleanWire G C b)
    {A B : Finset (Fin n)} (hA : RawForm C r a A false) (hB : RawForm C r b B false)
    (hdisj : Disjoint A B) (hcardA : 1 < A.card) (hcardB : 1 < B.card)
    (hprod : ∀ x : Fin n → Bool, val C (List.ofFn x) (n+r) = true ↔ hits A x ∧ hits B x)
    {s : Fin n} (hs : s ∈ A)
    (hcolA : ∀ z ∈ A, colour z = colour s) (hcolB : ∀ z ∈ B, colour z ≠ colour s)
    {j p q : ℕ} (hj : j < C.gates.length) (hja : (gateAt C j).op = GateOp.and)
    (hjc : BelowF G C j) {S T : Finset (Fin n)}
    (hpq : (gateAt C j).inputs = [p,q] ∨ (gateAt C j).inputs = [q,p])
    (hS : RawForm C r p S true) (hT : RawForm C r q T false)
    (path : OrCarrierRoute n C r i p) (hsT : s ∈ T) : False := by
  classical
  let W := suspendedValue (n := n) C r (fun _ => false)
  have hW : EvalExcept n C r W := suspendedValue_evalExcept C h.1 r _
  have hzero (x) : W x (n+r) = false := suspendedValue_hole C r _ x
  have ht := routedTopSemantics hj (cleanDifferent G C hJ hjc) hja hpq hS hT
  have star (z : Fin n) (hz : z ∈ B) : G.Adj s z :=
    (carrierCross G h.1 hprod hjc ht hs hz hsT (Or.inr rfl) (Or.inl rfl)).symm
  have sameColour (u v w : Fin n) (hu : colour u ≠ colour w)
      (hv : colour v ≠ colour w) : colour u = colour v := by
    generalize colour u = cu at hu ⊢
    generalize colour v = cv at hv ⊢
    generalize colour w = cw at hu hv
    cases cu <;> cases cv <;> cases cw <;> simp_all
  have rawCross {k : ℕ} {P Q : Finset (Fin n)} (hc : BelowF G C k)
      (ht : OrientedTop C r k P Q true) {u v : Fin n} (hu : u ∈ P) (hv : v ∈ Q) :
      G.Adj u v := adjOfPair G (hc _ ((ht _ (originalEvalExcept h.1 r) (pairInput u v)).mpr
        ⟨Or.inl ⟨u,hu,by simp [pairInput]⟩,⟨v,hv,by simp [pairInput]⟩⟩))
  have colTop {k u w t : ℕ} (hk : k < C.gates.length) (hka : (gateAt C k).op = GateOp.and)
      (hkc : BelowF G C k) {P Q : Finset (Fin n)}
      (huw : (gateAt C k).inputs = [u,w] ∨ (gateAt C k).inputs = [w,u])
      (hP : RawForm C r u P true) (hQ : RawForm C r w Q false)
      (route : OrCarrierRoute n C r t u) : ∀ c ∈ Q, colour c = colour s := by
    obtain ⟨htl,_,htm⟩ := routeReadSite route
    have he := only t htl htm
    obtain ⟨e,heS,heP⟩ := carrierRoutesShareRawLeaf G C h hl hJ hi hio hir path (he ▸ route) hS hP
    have htop := routedTopSemantics hk (cleanDifferent G C hJ hkc) hka huw hP hQ
    intro c hc
    exact sameColour c s e (hcolour c e (rawCross hkc htop heP hc).symm)
      (hcolour s e (rawCross hjc ht heS hsT).symm)
  have cover (u v : Fin n) (huv : G.Adj u v) : W (pairInput u v) C.output = true ∨
      (pairInput u v s = true ∧ hits B (pairInput u v)) := by
    let x := pairInput u v
    by_cases ho : W x C.output = true
    · exact Or.inl ho
    have hf : W x C.output = false := by
      cases he : W x C.output
      · rfl
      · exact (ho he).elim
    obtain ⟨t,k,u',w,P,Q,_,_,_,hk,hka,hkc,huw,hP,hQ,route,hQx⟩ :=
      lostRoutedTop G C h hl hJ hno hW x (pair_true G u v huv) hf
    obtain ⟨⟨a',ha',hax⟩,⟨b',hb',hbx⟩⟩ :=
      (hprod x).mp (lostPositiveJunk G C h hl hJ hW x (pair_true G u v huv) hf)
    obtain ⟨c,hc,hcx⟩ := hQx
    have hne : a' ≠ b' := fun he => Finset.disjoint_left.mp hdisj ha' (he.symm ▸ hb')
    have h1 : a' = u ∨ a' = v := by simpa [x,pairInput] using hax
    have h2 : b' = u ∨ b' = v := by simpa [x,pairInput] using hbx
    have h3 : c = u ∨ c = v := by simpa [x,pairInput] using hcx
    have hc' : c = a' ∨ c = b' := memberOfPair h1 h2 h3 hne
    have hcA : c ∈ A := by
      rcases hc' with he | he
      · exact he.symm ▸ ha'
      · exact (hcolB b' hb' (he ▸ colTop hk hka hkc huw hP hQ route c hc)).elim
    have hkTop := routedTopSemantics hk (cleanDifferent G C hJ hkc) hka huw hP hQ
    have starC (z : Fin n) (hz : z ∈ B) : G.Adj c z :=
      (carrierCross G h.1 hprod hkc hkTop hcA hz hc (Or.inr rfl) (Or.inl rfl)).symm
    obtain ⟨e,he,f,hf',hef⟩ := Finset.one_lt_card.mp hcardB
    have hcs := commonNeighborUnique G h4 hef (star e he).symm (star f hf').symm
      (starC e he).symm (starC f hf').symm
    exact Or.inr ⟨hcs ▸ hcx,b',hb',hbx⟩
  by_cases huse : ResidualUse G C r (W (fun _ => true)) a
  · obtain ⟨d,hd⟩ := residualUseCoversSupport G C h hl hJ hW hzero huse
      (fun x hx => (hA.2 W hW x).mpr (Or.inl hx))
    have universal (z : Fin n) (hz : ∀ y ∈ A, G.Adj y z) : z = d := by
      obtain ⟨e,he,f,hf,hef⟩ := Finset.one_lt_card.mp hcardA
      exact commonNeighborUnique G h4 hef (hd e he).1 (hd f hf).1 (hz e he) (hz f hf)
    have existsBad : ∃ z ∈ B, ¬ ∀ y ∈ A, G.Adj y z := by
      by_contra! hall
      obtain ⟨e,he,f,hf,hef⟩ := Finset.one_lt_card.mp hcardB
      exact hef ((universal e (hall e he)).trans (universal f (hall f hf)).symm)
    obtain ⟨t,htB,htbad⟩ := existsBad
    have forced {k u w i' : ℕ} (hk : k < C.gates.length) (hka : (gateAt C k).op = GateOp.and)
        (hkc : BelowF G C k) {P Q : Finset (Fin n)}
        (huw : (gateAt C k).inputs = [u,w] ∨ (gateAt C k).inputs = [w,u])
        (hP : RawForm C r u P true) (hQ : RawForm C r w Q false)
        (route : OrCarrierRoute n C r i' u) {z : Fin n} (hzB : z ∈ B)
        (hbad : ¬ ∀ y ∈ A, G.Adj y z) : ∀ c ∈ Q, G.Adj c z := by
      push Not at hbad
      obtain ⟨y,hy,hyn⟩ := hbad
      intro c hc
      have hyc : colour y = colour c := (hcolA y hy).trans (colTop hk hka hkc huw hP hQ route c hc).symm
      let x : Fin n → Bool := fun w => decide (w = y ∨ w = z ∨ w = c)
      have htop := routedTopSemantics hk (cleanDifferent G C hJ hkc) hka huw hP hQ
      have hpos : graphFun G ∅ x = true := hkc x ((htop _ (originalEvalExcept h.1 r) x).mpr
        ⟨Or.inr ⟨rfl,(hprod x).mpr ⟨⟨y,hy,by simp [x]⟩,⟨z,hzB,by simp [x]⟩⟩⟩,
          ⟨c,hc,by simp [x]⟩⟩)
      obtain ⟨l,m,hlm,hlx,hmx⟩ := (graph_true G x).mp hpos
      have hl' : l = y ∨ l = z ∨ l = c := by simpa [x] using hlx
      have hm' : m = y ∨ m = z ∨ m = c := by simpa [x] using hmx
      rcases hl' with hl' | hl' | hl' <;> rcases hm' with hm' | hm' | hm' <;> rw [hl',hm'] at hlm
      · exact (G.ne_of_adj hlm rfl).elim
      · exact (hyn hlm).elim
      · exact (hcolour y c hlm hyc).elim
      · exact (hyn hlm.symm).elim
      · exact (G.ne_of_adj hlm rfl).elim
      · exact hlm.symm
      · exact (hcolour c y hlm hyc.symm).elim
      · exact hlm
      · exact (G.ne_of_adj hlm rfl).elim
    by_cases hsecond : ∃ z ∈ B, z ≠ t ∧ ¬ ∀ y ∈ A, G.Adj y z
    · obtain ⟨z,hz,hzt,hbad⟩ := hsecond
      apply noOneJunkSiteReplacement G C h hl hJ hno (fun _ => b) (fun _ => hbl) hW hzero
      · intro k hk hka hkc u w P Q huw hP hQ i' route x hf hQx
        obtain ⟨c,hc,hcx⟩ := hQx
        have hcs := commonNeighborUnique G h4 hzt (star z hz).symm (star t htB).symm
          (forced hk hka hkc huw hP hQ route hz hbad c hc).symm
          (forced hk hka hkc huw hP hQ route htB htbad c hc).symm
        obtain ⟨v,hv,hvx⟩ := ((hB.2 _ (originalEvalExcept h.1 r) x).mp hf).resolve_right (by simp)
        exact (graph_true G x).mpr ⟨s,v,star v hv,hcs ▸ hcx,hvx⟩
      · intro u v huv hf i' _
        rcases cover u v huv with ho | ⟨_,hBhit⟩
        · rw [hf] at ho
          cases ho
        · exact (hB.2 _ (originalEvalExcept h.1 r) _).mpr (Or.inl hBhit)
    · have other (z : Fin n) (hz : z ∈ B) (hne : z ≠ t) : z = d :=
        universal z (by by_contra hn; exact hsecond ⟨z,hz,hne,hn⟩)
      apply noOneJunkSiteReplacement G C h hl hJ hno (fun _ => t.val)
        (fun _ => by have := t.isLt; omega) hW hzero
      · intro k hk hka hkc u w P Q huw hP hQ i' route x hf hQx
        obtain ⟨c,hc,hcx⟩ := hQx
        exact (graph_true G x).mpr ⟨c,t,forced hk hka hkc huw hP hQ route htB htbad c hc,hcx,
          ((originalEvalExcept h.1 r).1 x t).symm.trans hf⟩
      · intro u v huv hf i' _
        rcases cover u v huv with ho | ⟨hsx,z,hz,hzx⟩
        · rw [hf] at ho
          cases ho
        · by_cases he : z = t
          · exact ((originalEvalExcept h.1 r).1 _ t).trans (he ▸ hzx)
          · have heq := other z hz he
            have hp := pairEqOfHits u v s z hsx hzx (G.ne_of_adj (star z hz))
            have hw := (hd s hs).2
            rw [← heq,← hp,hf] at hw
            cases hw
  · exact exclusiveProviderOneStar G C h hl hJ hi hir hal hbl hbd hA hB hdisj hcardA hs star huse cover

set_option maxHeartbeats 1000000 in
/-- All sole OR-reader configurations with the verified disjoint large
    opposite-colour supports. Choose a genuinely lost edge to orient the
    seed star, then apply the one-carrier contradiction. -/
theorem noSoleOrReaderLargeSupports {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    (h4 : NoFourCycle G) (colour : Fin n → Bool)
    (hcolour : ∀ u v, G.Adj u v → colour u ≠ colour v)
    {r i a b : ℕ} (hJ : junk G C = {r})
    (hno : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → n+r ∉ (gateAt C j).inputs)
    (hi : i < C.gates.length) (hio : (gateAt C i).op = GateOp.or)
    (hir : n+r ∈ (gateAt C i).inputs)
    (only : ∀ k < C.gates.length, n+r ∈ (gateAt C k).inputs → k = i)
    (hab : (gateAt C r).inputs = [a,b])
    {A B : Finset (Fin n)} (hA : RawForm C r a A false) (hB : RawForm C r b B false)
    (hdisj : Disjoint A B) (hcardA : 1 < A.card) (hcardB : 1 < B.card)
    (col : Bool) (hcolA : ∀ z ∈ A, colour z = col) (hcolB : ∀ z ∈ B, colour z ≠ col) : False := by
  classical
  obtain ⟨hr,hand,_⟩ := junkMember G C hJ
  have hprod := originalJunkProduct h.1 hr hand hab hA hB
  let W := suspendedValue (n := n) C r (fun _ => false)
  have hW : EvalExcept n C r W := suspendedValue_evalExcept C h.1 r _
  have hzero (x) : W x (n+r) = false := suspendedValue_hole C r _ x
  by_cases hall : ∀ u v, G.Adj u v → W (pairInput u v) C.output = true
  · exact noOneJunkWithoutLostEdges G C h hl hJ hW hzero hall
  have hmissing : ∃ u v, G.Adj u v ∧ W (pairInput u v) C.output = false := by
    by_contra hnone
    apply hall
    intro u v huv
    cases he : W (pairInput u v) C.output
    · exact (hnone ⟨u,v,huv,he⟩).elim
    · rfl
  obtain ⟨u,v,huv,hf⟩ := hmissing
  obtain ⟨t,j,p,q,S,T,htl,_,htm,hj,hja,hjc,hpq,hS,hT,route,hTx⟩ :=
    lostRoutedTop G C h hl hJ hno hW (pairInput u v) (pair_true G u v huv) hf
  have hroute : OrCarrierRoute n C r i p := only t htl htm ▸ route
  obtain ⟨s,hsT,hsx⟩ := hTx
  obtain ⟨⟨y,hy,hyx⟩,⟨z,hz,hzx⟩⟩ := (hprod _).mp
    (lostPositiveJunk G C h hl hJ hW _ (pair_true G u v huv) hf)
  have hyz : y ≠ z := fun he => Finset.disjoint_left.mp hdisj hy (he.symm ▸ hz)
  have h1 : y = u ∨ y = v := by simpa [pairInput] using hyx
  have h2 : z = u ∨ z = v := by simpa [pairInput] using hzx
  have h3 : s = u ∨ s = v := by simpa [pairInput] using hsx
  have hs' : s = y ∨ s = z := memberOfPair h1 h2 h3 hyz
  have hal := h.1.2.1 r hr a (by simp [hab])
  have hbl := h.1.2.1 r hr b (by simp [hab])
  have had := noCleanAndOperand G C h r a hr (by simp [hab]) hand
  have hbd := noCleanAndOperand G C h r b hr (by simp [hab]) hand
  rcases hs' with he | he
  · have hsA : s ∈ A := he.symm ▸ hy
    exact noSoleOrReaderOfSeed G C h hl h4 colour hcolour hJ hno hi hio hir only hal hbl hbd
      hA hB hdisj hcardA hcardB hprod hsA (fun w hw => (hcolA w hw).trans (hcolA s hsA).symm)
      (fun w hw hn => hcolB w hw (hn.trans (hcolA s hsA))) hj hja hjc hpq hS hT hroute hsT
  · have hsB : s ∈ B := he.symm ▸ hz
    have hBsame (w) (hw : w ∈ B) : colour w = colour s := by
      have h1 := hcolB w hw
      have h2 := hcolB s hsB
      generalize colour w = cw at h1 ⊢
      generalize colour s = cs at h2 ⊢
      cases cw <;> cases cs <;> cases col <;> simp_all
    exact noSoleOrReaderOfSeed G C h hl h4 colour hcolour hJ hno hi hio hir only hbl hal had
      hB hA hdisj.symm hcardB hcardA (fun x => (hprod x).trans and_comm) hsB hBsame
      (fun w hw hn => hcolB s hsB (hn.symm.trans (hcolA w hw))) hj hja hjc hpq hS hT hroute hsT

#print axioms noSoleOrReaderLargeSupports


/-! Many-junk descent: the last dirty AND with a unique pivotal edge.
    The following comparison and normalization do not assume a singleton junk set. -/

/-- Two suspended evaluations are ordered (or equal) if their fill values
    are ordered (or equal). This is independent of the other dirty ANDs. -/
private theorem evalExceptRel {n : ℕ} {C : Circuit} (h : IsAO2 n C)
    {r : ℕ} {V W : (Fin n → Bool) → ℕ → Bool}
    (hV : EvalExcept n C r V) (hW : EvalExcept n C r W)
    {R : Bool → Bool → Prop} (hrefl : ∀ b, R b b) (hmono : OpMono R)
    (x : Fin n → Bool) (hfill : R (V x (n+r)) (W x (n+r))) :
    ∀ w < n+C.gates.length, R (V x w) (W x w) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hn : w < n
    · let v : Fin n := ⟨w,hn⟩
      rw [hV.1 x v,hW.1 x v]
      exact hrefl _
    obtain ⟨j,rfl⟩ : ∃ j, w = n+j := ⟨w-n,by omega⟩
    by_cases he : j = r
    · subst j
      exact hfill
    have hj : j < C.gates.length := by omega
    rw [hV.2 x j hj he,hW.2 x j hj he]
    apply hmono _ (h.1 _ (gateAt_mem hj))
    intro p hp
    have hlt := h.2.1 j hj p hp
    exact ih p hlt (by omega)

/-- Every gate of a least circuit is pivotal on at least one edge input.
    Otherwise its false suspension compiles to a strictly smaller circuit. -/
theorem everyGateHasLostEdge {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (h : IsLeastAO G C)
    {r : ℕ} (hr : r < C.gates.length)
    {W : (Fin n → Bool) → ℕ → Bool} (hW : EvalExcept n C r W)
    (hz : ∀ x, W x (n+r) = false) :
    ∃ u v, G.Adj u v ∧ W (pairInput u v) C.output = false := by
  classical
  have hout := outputLast G C h (by omega : 0 < C.gates.length)
  have hob : C.output < n+C.gates.length := by omega
  by_contra hn
  have hcover (u v : Fin n) (huv : G.Adj u v) : W (pairInput u v) C.output = true := by
    cases he : W (pairInput u v) C.output
    · exact (hn ⟨u,v,huv,he⟩).elim
    · rfl
  have hsound (x : Fin n → Bool) (hx : W x C.output = true) :
      graphFun G ∅ x = true := by
    have hle := evalExceptRel h.1 hW (originalEvalExcept h.1 r)
      (R := fun a b => a = true → b = true) (fun _ => id) opMono_imp x
      (by rw [hz x]; intro hf; cases hf) C.output hob hx
    exact (congrFun h.2.1 x).symm ▸ hle
  obtain ⟨D₀,hD₀,hlen,hwires⟩ := compileFalseSuspension C h.1 hW hz {r}
    (by simpa using hr) (by intro j hj; exact Or.inl (Finset.mem_singleton.mp hj))
  have hlen' : D₀.gates.length+1 ≤ C.gates.length := by simpa using hlen
  rcases hwires C.output hob with hf | ⟨w,_,hw⟩
  · have he (u v : Fin n) (huv : G.Adj u v) : False :=
      Bool.false_ne_true ((hf _).symm.trans (hcover u v huv))
    have := emptyGraphNoGates G C h he
    omega
  · let D : Circuit := ⟨D₀.gates,w⟩
    have hD : IsAO2 n D := hD₀
    have hv (x : Fin n → Bool) : circuitFun n D x = W x C.output := hw x
    have hc : circuitFun n D = graphFun G ∅ := by
      funext x
      apply Bool.eq_iff_iff.mpr
      refine ⟨fun hx => hsound x ((hv x).symm.trans hx),?_⟩
      intro hx
      obtain ⟨u,v,huv,hu,hv'⟩ := (graph_true G x).mp hx
      apply circuit_monotone n D (ao_mono hD) (pairInput u v) x ?_ ((hv _).trans (hcover u v huv))
      intro z hz'
      rcases (show z = u ∨ z = v by simpa [pairInput] using hz') with rfl | rfl
      · exact hu
      · exact hv'
    have hm := h.2.2 D hD hc
    change C.gates.length ≤ D₀.gates.length at hm
    omega

/-- Membership in the dirty AND set, with no cardinality hypothesis. -/
private lemma memJunkIff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (j : ℕ) :
    j ∈ junk G C ↔ j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧ ¬ BelowF G C j := by
  constructor
  · intro hm
    simp only [junk, gatesWhere, Finset.mem_filter, Finset.mem_range] at hm
    obtain ⟨hj, ha, _, x, hx, hf⟩ := hm
    exact ⟨hj, ha, fun hc => by have hh := hc x hx; rw [hf] at hh; contradiction⟩
  · rintro ⟨hj, ha, hd⟩
    have hdirty : PEqualNP.CleanedNonEdge.IsDirty n G C j := by
      refine ⟨hj, ?_⟩
      by_contra hn
      apply hd
      intro x hx
      cases hf : graphFun G ∅ x with
      | true => rfl
      | false => exact (hn ⟨x, hx, hf⟩).elim
    simp only [junk, gatesWhere, Finset.mem_filter, Finset.mem_range]
    exact ⟨hj, ha, hdirty⟩

/-- Replace one gate by a raw edge conjunction, keeping all other indices.
    If false suspension loses only that edge, this is an exact same-size
    rewrite, even if many earlier dirty ANDs feed the chosen gate. -/
theorem singleLostEdgeRewrite {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) {r : ℕ} (hr : r < C.gates.length)
    {W : (Fin n → Bool) → ℕ → Bool} (hW : EvalExcept n C r W)
    (hz : ∀ x, W x (n+r) = false)
    {a b : Fin n} (hab : G.Adj a b) (hmiss : W (pairInput a b) C.output = false)
    (honly : ∀ u v, G.Adj u v → W (pairInput u v) C.output = false →
      pairInput u v = pairInput a b) :
    ∃ D : Circuit, IsLeastAO G D ∧ D.gates.length = C.gates.length ∧
      (∀ j < C.gates.length, j ≠ r → gateAt D j = gateAt C j) ∧
      (gateAt D r).op = GateOp.and ∧ BelowF G D r ∧
      (∀ j < C.gates.length, BelowF G C j → BelowF G D j) := by
  classical
  let D : Circuit := ⟨(List.range C.gates.length).map (fun j =>
    if j = r then ⟨GateOp.and,[a.val,b.val]⟩ else gateAt C j),C.output⟩
  have hlen : D.gates.length = C.gates.length := by simp [D]
  have hg (j) (hj : j < C.gates.length) :
      gateAt D j = if j = r then ⟨GateOp.and,[a.val,b.val]⟩ else gateAt C j := by
    rw [gateAt_eq (by omega : j < D.gates.length)]
    simp [D]
  have heq (j) (hj : j < C.gates.length) (hne : j ≠ r) : gateAt D j = gateAt C j := by
    rw [hg j hj,ite_eq_right hne]
  have hnew : gateAt D r = ⟨GateOp.and,[a.val,b.val]⟩ := by rw [hg r hr,ite_eq_left rfl]
  have hD : IsAO2 n D := by
    refine ⟨?_,?_,?_⟩
    · intro g hm
      rcases List.mem_map.mp hm with ⟨j,hj,rfl⟩
      have hj' := List.mem_range.mp hj
      split_ifs
      · exact Or.inl rfl
      · exact h.1.1 _ (gateAt_mem hj')
    · intro j hj w hw
      have hj' : j < C.gates.length := by omega
      rw [hg j hj'] at hw
      split_ifs at hw with hjr
      · rcases (show w = a.val ∨ w = b.val by simpa using hw) with rfl | rfl
        · have := a.isLt; omega
        · have := b.isLt; omega
      · exact h.1.2.1 j hj' w hw
    · intro g hm
      rcases List.mem_map.mp hm with ⟨j,hj,rfl⟩
      have hj' := List.mem_range.mp hj
      split_ifs
      · rfl
      · exact h.1.2.2 _ (gateAt_mem hj')
  let V := fun (x : Fin n → Bool) w => val C (List.ofFn x) w
  let Z := fun (x : Fin n → Bool) w => val D (List.ofFn x) w
  have hV : EvalExcept n C r V := originalEvalExcept h.1 r
  have hZ : EvalExcept n C r Z := by
    refine ⟨(originalEvalExcept hD r).1,?_⟩
    intro x j hj hne
    have he := (originalEvalExcept hD r).2 x j (by omega) hne
    rw [heq j hj hne] at he
    exact he
  have hfill (x : Fin n → Bool) : Z x (n+r) = true ↔ x a = true ∧ x b = true := by
    change val D (List.ofFn x) (n+r) = true ↔ _
    rw [val_gate (n := n) (by simp) (show r < D.gates.length by omega),hnew]
    have ha : a.val < n+r := by have := a.isLt; omega
    have hb : b.val < n+r := by have := b.isLt; omega
    simp [GateOp.eval,ha,hb,(originalEvalExcept hD r).1 x a,(originalEvalExcept hD r).1 x b]
  have hout := outputLast G C h (by omega : 0 < C.gates.length)
  have hob : C.output < n+C.gates.length := by omega
  have hpiv : V (pairInput a b) (n+r) = true := by
    cases he : V (pairInput a b) (n+r)
    · have heq' := evalExceptRel h.1 hV hW (R := Eq) (fun _ => rfl) opMono_eq
        (pairInput a b) (he.trans (hz _).symm) C.output hob
      have ht : V (pairInput a b) C.output = true := (congrFun h.2.1 _).trans (pair_true G a b hab)
      rw [ht,hmiss] at heq'
      cases heq'
    · rfl
  have hle (x : Fin n → Bool) : ∀ w < n+C.gates.length, Z x w = true → V x w = true := by
    apply evalExceptRel h.1 hZ hV (R := fun a b => a = true → b = true) (fun _ => id) opMono_imp x
    intro ht
    obtain ⟨ha,hb⟩ := (hfill x).mp ht
    apply wire_monotone n C (ao_mono h.1) (pairInput a b) x ?_ _ hpiv
    intro z hzx
    rcases (show z = a ∨ z = b by simpa [pairInput] using hzx) with rfl | rfl
    · exact ha
    · exact hb
  have hWZ (x : Fin n → Bool) : ∀ w < n+C.gates.length, W x w = true → Z x w = true :=
    evalExceptRel h.1 hW hZ (R := fun a b => a = true → b = true) (fun _ => id) opMono_imp x
      (by rw [hz x]; intro hf; cases hf)
  have hedge (u v : Fin n) (huv : G.Adj u v) : Z (pairInput u v) C.output = true := by
    cases he : W (pairInput u v) C.output
    · have hp := honly u v huv he
      rw [hp]
      have hf : Z (pairInput a b) (n+r) = true := (hfill _).mpr (by simp [pairInput])
      have heq' := evalExceptRel h.1 hZ hV (R := Eq) (fun _ => rfl) opMono_eq
        (pairInput a b) (hf.trans hpiv.symm) C.output hob
      exact heq'.trans ((congrFun h.2.1 _).trans (pair_true G a b hab))
    · exact hWZ _ _ hob he
  have hc : circuitFun n D = graphFun G ∅ := by
    funext x
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hx
      have ht : Z x C.output = true := hx
      exact (congrFun h.2.1 x).symm ▸ hle x _ hob ht
    · intro hx
      obtain ⟨u,v,huv,hu,hv⟩ := (graph_true G x).mp hx
      apply circuit_monotone n D (ao_mono hD) (pairInput u v) x ?_ (hedge u v huv)
      intro z hz'
      rcases (show z = u ∨ z = v by simpa [pairInput] using hz') with rfl | rfl
      · exact hu
      · exact hv
  have hleast : IsLeastAO G D := ⟨hD,hc,fun E hE hEq => by
    have hm := h.2.2 E hE hEq
    change D.gates.length ≤ E.gates.length
    change C.gates.length ≤ E.gates.length at hm
    omega⟩
  refine ⟨D,hleast,hlen,heq,congrArg Gate.op hnew,?_,?_⟩
  · intro x hx
    obtain ⟨ha,hb⟩ := (hfill x).mp hx
    exact (graph_true G x).mpr ⟨a,b,hab,ha,hb⟩
  · intro j hj hjc x hx
    exact hjc x (hle x _ (by omega) hx)

/-- Move an implicant out of a dirty OR to a new final collector OR.
    All retained gates keep their operators, and clean retained gates
    stay clean by pointwise decrease. This is an equal-size lift. -/
private theorem suffixLiftStep {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D : Circuit) (h : IsLeastAO G D) {k q : ℕ} (hk : k < D.gates.length)
    (hor : (gateAt D k).op = GateOp.or) (hq : q ∈ (gateAt D k).inputs)
    (hclean : CleanWire G D q) :
    ∃ E : Circuit, IsLeastAO G E ∧ E.gates.length = D.gates.length ∧
      (∀ j < k, gateAt E j = gateAt D j) ∧
      (∀ j < D.gates.length-1,
        let t := if j < k then j else j+1
        (gateAt E j).op = (gateAt D t).op ∧ (BelowF G D t → BelowF G E j)) ∧
      (gateAt E (D.gates.length-1)).op = GateOp.or ∧ BelowF G E (D.gates.length-1) := by
  obtain ⟨a,b,hab⟩ := twoOperands h.1 hk
  have hq' : q = a ∨ q = b := by simpa [hab] using hq
  obtain ⟨p,hpq⟩ : ∃ p, (gateAt D k).inputs = [p,q] ∨ (gateAt D k).inputs = [q,p] := by
    rcases hq' with rfl | rfl
    · exact ⟨b,Or.inr hab⟩
    · exact ⟨a,Or.inl hab⟩
  have hp : p ∈ (gateAt D k).inputs := by rcases hpq with he | he <;> simp [he]
  have hpl := h.1.2.1 k hk p hp
  have hql := h.1.2.1 k hk q hq
  let B := bypass n D k p
  have hBlen : B.gates.length = D.gates.length-1 := bypass_length n D k p
  have hB : IsAO2 n B := by
    change IsAO2 n (bypass n D k p)
    rw [← erase_eq_bypass n D k p hk]
    exact erase_exactAO h.1 hk hpl
  have hout := outputLast G D h (by omega : 0 < D.gates.length)
  have hob : B.output < n+B.gates.length := by
    change aliasWire (n+k) p D.output < n+B.gates.length
    exact aliasWire_lt hpl (by omega) (by omega)
  have hqb : q < n+B.gates.length := by omega
  let A := appendBinary B GateOp.or B.output q
  obtain ⟨hAlen,hA,hkeep,hfresh⟩ := appendBinary_spec hB (Or.inr rfl) hob hqb
  let E : Circuit := ⟨A.gates,n+B.gates.length⟩
  have hE : IsAO2 n E := hA
  have hAlen' : A.gates.length = B.gates.length+1 := hAlen
  have hlen : E.gates.length = D.gates.length := by
    change A.gates.length = D.gates.length
    rw [hAlen',hBlen]
    omega
  have hqval (x : Fin n → Bool) : val B (List.ofFn x) q = val D (List.ofFn x) q :=
    bypass_val_lt (n := n) (by simp) hk q hql
  have hval (x : Fin n → Bool) : circuitFun n E x =
      (circuitFun n B x || val D (List.ofFn x) q) := by
    change val A (List.ofFn x) (n+B.gates.length) = _
    rw [hfresh x,hqval]
    change GateOp.or.eval [val B (List.ofFn x) B.output,val D (List.ofFn x) q] =
      (val B (List.ofFn x) B.output || val D (List.ofFn x) q)
    simp [GateOp.eval]
  have hAO := mono_ops (ao_mono h.1)
  have hdec (x : Fin n → Bool) :
      val D (List.ofFn x) p = true → val D (List.ofFn x) (n+k) = true :=
    fun ht => (val_or (n := n) (by simp) hk hor).mpr ⟨p,hp,hpl,ht⟩
  have hres (x : Fin n → Bool) : circuitFun n B x = true → circuitFun n D x = true :=
    bypass_eval_rel (R := fun a b => b = true → a = true) (fun _ => id) opMono_reverse
      (n := n) (by simp) hAO hk (Or.inl hpl) (hdec x)
  have hrest (x : Fin n → Bool) (hqf : val D (List.ofFn x) q = false) :
      circuitFun n B x = circuitFun n D x := by
    apply bypass_eval_eq (n := n) (by simp) hAO hk (Or.inl hpl)
    apply Bool.eq_iff_iff.mpr
    refine ⟨?_,hdec x⟩
    intro ht
    obtain ⟨w,hw,_,hv⟩ := (val_or (n := n) (by simp) hk hor).mp ht
    have he : w = p ∨ w = q := by rcases hpq with h | h <;> rw [h] at hw <;> simpa [or_comm] using hw
    rcases he with rfl | rfl
    · exact hv
    · rw [hqf] at hv
      cases hv
  have hc : circuitFun n E = graphFun G ∅ := by
    funext x
    rw [hval]
    cases he : val D (List.ofFn x) q
    · rw [hrest x he,congrFun h.2.1 x]
      simp
    · rw [hclean x he]
      simp
  have hleast : IsLeastAO G E := ⟨hE,hc,fun F hF hf => by
    have hm := h.2.2 F hF hf
    change E.gates.length ≤ F.gates.length
    change D.gates.length ≤ F.gates.length at hm
    omega⟩
  have old (j) (hj : j < B.gates.length) : gateAt E j = gateAt B j := by
    rw [gateAt_eq (by omega : j < E.gates.length),gateAt_eq hj]
    exact List.getElem_append_left hj
  have fresh : gateAt E (D.gates.length-1) = ⟨GateOp.or,[B.output,q]⟩ := by
    rw [← hBlen,gateAt_eq (by omega : B.gates.length < E.gates.length)]
    simp [E,A,appendBinary,List.getElem_append_right (le_refl B.gates.length)]
  refine ⟨E,hleast,hlen,?_,?_,congrArg Gate.op fresh,?_⟩
  · intro j hj
    rw [old j (by omega),gateAt_bypass (by omega),ite_eq_left hj]
  · intro j hj
    dsimp only
    have hgate := old j (by omega)
    by_cases hlt : j < k
    · rw [ite_eq_left hlt,hgate,gateAt_bypass hj,ite_eq_left hlt]
      refine ⟨rfl,?_⟩
      intro hcl x hx
      change val A (List.ofFn x) (n+j) = true at hx
      rw [hkeep x (n+j) (by omega),bypass_val_lt (n := n) (by simp) hk (n+j) (by omega)] at hx
      exact hcl x hx
    · rw [ite_eq_right hlt,hgate,gateAt_bypass hj,ite_eq_right hlt]
      refine ⟨rfl,?_⟩
      intro hcl x hx
      change val A (List.ofFn x) (n+j) = true at hx
      rw [hkeep x (n+j) (by omega)] at hx
      have hb := bypass_rel (R := fun a b => b = true → a = true) (fun _ => id) opMono_reverse
        (n := n) (by simp) hAO hk (Or.inl hpl) (fun _ => hdec x)
        (n+(j+1)) (by omega)
      rw [aliasWire_gt_self (by omega : n+k < n+(j+1)),show n+(j+1)-1 = n+j by omega] at hb
      exact hcl x (hb hx)
  · intro x hx
    have he : circuitFun n E x = true := by
      change val E (List.ofFn x) (n+B.gates.length) = true
      have hh : D.gates.length-1 = B.gates.length := hBlen.symm
      change val E (List.ofFn x) (n+(D.gates.length-1)) = true at hx
      rwa [hh] at hx
    exact (congrFun hc x).symm ▸ he

/-- Lift-normalize a same-size rewrite without touching its fixed prefix
    or introducing dirty ANDs in the suffix. The clean OR tail grows at
    every lift, giving termination with no appeal to a new axiom. -/
private theorem normalizeCleanAndSuffix {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    (m : ℕ) (hm : m ≤ C.gates.length) :
    ∀ d (D : Circuit) (t : ℕ), D.gates.length-t = d → IsLeastAO G D →
      D.gates.length = C.gates.length →
      (∀ j < m, gateAt D j = gateAt C j) →
      (∀ j < D.gates.length, m ≤ j → (gateAt D j).op = GateOp.and → BelowF G D j) →
      (∀ j < D.gates.length, D.gates.length-t ≤ j →
        (gateAt D j).op = GateOp.or ∧ BelowF G D j) →
      ∃ E : Circuit, IsLeastAO G E ∧ IsLiftFixedPoint G E ∧
        E.gates.length = C.gates.length ∧ (∀ j < m, gateAt E j = gateAt C j) ∧
        (∀ j < E.gates.length, m ≤ j → (gateAt E j).op = GateOp.and → BelowF G E j) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro D t hd hD hlen hpre hsuf htail
    by_cases hfix : IsLiftFixedPoint G D
    · exact ⟨D,hD,hfix,hlen,hpre,hsuf⟩
    have happ : LiftApplies G D := by
      by_contra hn
      exact hfix hn
    obtain ⟨k,hk,b,_,hor,hdirty,himp⟩ := happ
    have hq : opnd D k b ∈ (gateAt D k).inputs := by
      obtain ⟨a,c,hac⟩ := twoOperands hD.1 hk
      fin_cases b <;> simp [opnd,hac]
    have hcl : CleanWire G D (opnd D k b) := himp.1
    have hkt : k < D.gates.length-t := by
      by_contra! hn
      exact hdirty (htail k hk hn).2
    have hkm : m ≤ k := by
      by_contra! hn
      have hqbound := hD.1.2.1 k hk _ hq
      have hv (x : Fin n → Bool) (w : ℕ) (hw : w < n+m) :
          val D (List.ofFn x) w = val C (List.ofFn x) w :=
        val_prefix (n := n) (by simp) hm (by omega) hpre w hw
      have hcq : CleanWire G C (opnd D k b) := by
        intro x hx
        apply hcl x
        rw [hv x _ (by omega)]
        exact hx
      have hqC : opnd D k b ∈ (gateAt C k).inputs := by rwa [hpre k hn] at hq
      have hcc := (cleanWireReader G C h hl (by omega : k < C.gates.length) hqC hcq).2
      apply hdirty
      intro x hx
      change val D (List.ofFn x) (n+k) = true at hx
      rw [hv x _ (by omega)] at hx
      exact hcc x hx
    obtain ⟨E,hE,hEl,hEk,hops,hend,hendc⟩ := suffixLiftStep G D hD hk hor hq hcl
    have hEl' : E.gates.length = C.gates.length := hEl.trans hlen
    have hp (j) (hj : j < m) : gateAt E j = gateAt C j :=
      (hEk j (by omega)).trans (hpre j hj)
    have hS (j) (hj : j < E.gates.length) (hjm : m ≤ j) (hja : (gateAt E j).op = GateOp.and) :
        BelowF G E j := by
      by_cases hlast : j = D.gates.length-1
      · rw [hlast,hend] at hja
        cases hja
      have hj' : j < D.gates.length-1 := by omega
      have hh := hops j hj'
      dsimp only at hh
      let u := if j < k then j else j+1
      have hu : u < D.gates.length := by dsimp [u]; split_ifs <;> omega
      have hum : m ≤ u := by dsimp [u]; split_ifs <;> omega
      exact hh.2 (hsuf u hu hum (hh.1.symm.trans hja))
    have hT (j) (hj : j < E.gates.length) (hjt : E.gates.length-(t+1) ≤ j) :
        (gateAt E j).op = GateOp.or ∧ BelowF G E j := by
      by_cases hlast : j = D.gates.length-1
      · simpa [hlast] using And.intro hend hendc
      have hj' : j < D.gates.length-1 := by omega
      have hn : ¬ j < k := by omega
      have hh := hops j hj'
      dsimp only at hh
      rw [ite_eq_right hn] at hh
      obtain ⟨ho,hc⟩ := htail (j+1) (by omega) (by omega)
      exact ⟨hh.1.trans ho,hh.2 hc⟩
    exact ih (E.gates.length-(t+1)) (by omega) E (t+1) rfl hE hEl' hp hS hT

/-- A genuine one-step descent for the last dirty AND when its pivotal
    edge set is a singleton (unordered). No new dirty AND is introduced,
    the earlier ones survive verbatim, and lift-fixedness is restored. -/
theorem lastJunkSingleEdgeDescent {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    {r : ℕ} (hrJ : r ∈ junk G C) (hmax : ∀ j ∈ junk G C, j ≤ r)
    {W : (Fin n → Bool) → ℕ → Bool} (hW : EvalExcept n C r W)
    (hz : ∀ x, W x (n+r) = false)
    {a b : Fin n} (hab : G.Adj a b) (hmiss : W (pairInput a b) C.output = false)
    (honly : ∀ u v, G.Adj u v → W (pairInput u v) C.output = false →
      pairInput u v = pairInput a b) :
    ∃ E : Circuit, IsLeastAO G E ∧ IsLiftFixedPoint G E ∧
      E.gates.length = C.gates.length ∧ junk G E = (junk G C).erase r := by
  classical
  have hr := ((memJunkIff G C r).mp hrJ).1
  obtain ⟨D,hD,hlen,hg,_,hclean,hkeep⟩ :=
    singleLostEdgeRewrite G C h hr hW hz hab hmiss honly
  have hpre (j) (hj : j < r) : gateAt D j = gateAt C j :=
    hg j (by omega) (by omega)
  have hsuf (j) (hj : j < D.gates.length) (hjr : r ≤ j)
      (ha : (gateAt D j).op = GateOp.and) : BelowF G D j := by
    by_cases he : j = r
    · simpa [he] using hclean
    have hj' : j < C.gates.length := by omega
    apply hkeep j hj'
    by_contra hn
    have hmem := (memJunkIff G C j).mpr ⟨hj',(hg j hj' he).symm ▸ ha,hn⟩
    have := hmax j hmem
    omega
  obtain ⟨E,hE,hfix,hEl,hEp,hEs⟩ :=
    normalizeCleanAndSuffix G C h hl r (by omega) D.gates.length D 0 (by simp)
      hD hlen hpre hsuf (by intro j hj ht; omega)
  refine ⟨E,hE,hfix,hEl,?_⟩
  ext j
  rw [Finset.mem_erase,memJunkIff,memJunkIff]
  by_cases hj : j < r
  · have hv (x : Fin n → Bool) :
        val E (List.ofFn x) (n+j) = val C (List.ofFn x) (n+j) :=
      val_prefix (n := n) (by simp) (by omega) (by omega) hEp _ (by omega)
    have hc : BelowF G E j ↔ BelowF G C j := by
      constructor
      · intro ht x hx
        apply ht x
        change val E (List.ofFn x) (n+j) = true
        rw [hv x]
        exact hx
      · intro ht x hx
        apply ht x
        change val C (List.ofFn x) (n+j) = true
        change val E (List.ofFn x) (n+j) = true at hx
        rwa [hv x] at hx
    rw [hEp j hj,hc,hEl]
    exact ⟨fun ht => ⟨by omega,ht⟩,fun ht => ht.2⟩
  · constructor
    · rintro ⟨hj',ha,hd⟩
      exact (hd (hEs j hj' (by omega) ha)).elim
    · rintro ⟨hne,hj',ha,hd⟩
      have hh := hmax j ((memJunkIff G C j).mpr ⟨hj',ha,hd⟩)
      omega

#print axioms everyGateHasLostEdge
#print axioms singleLostEdgeRewrite
#print axioms lastJunkSingleEdgeDescent


/-! Multi-edge descent by a prefix-preserving false-suspension repair.
    A repair can use any two available residual wires, not just raw ORs. -/

private def CleanExtension {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D E : Circuit) : Prop :=
  D.gates.length ≤ E.gates.length ∧
  (∀ j < D.gates.length, gateAt E j = gateAt D j) ∧
  ∀ j < E.gates.length, D.gates.length ≤ j →
    (gateAt E j).op = GateOp.and → BelowF G E j

private lemma cleanExtensionRefl {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D : Circuit) : CleanExtension G D D :=
  ⟨le_rfl, fun _ _ => rfl, fun _ hj hge _ => (Nat.not_lt_of_ge hge hj).elim⟩

private lemma cleanExtensionWires {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {D E : Circuit} (h : CleanExtension G D E) : PreservesWires n D E :=
  ⟨h.1, fun x w hw => val_prefix (n := n) (by simp) le_rfl h.1 h.2.1 w hw⟩

private lemma cleanExtensionTrans {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {D E F : Circuit} (hDE : CleanExtension G D E) (hEF : CleanExtension G E F) :
    CleanExtension G D F := by
  refine ⟨hDE.1.trans hEF.1, ?_, ?_⟩
  · intro j hj
    exact (hEF.2.1 j (lt_of_lt_of_le hj hDE.1)).trans (hDE.2.1 j hj)
  · intro j hj hge hand
    by_cases hlt : j < E.gates.length
    · have hc := hDE.2.2 j hlt hge ((hEF.2.1 j hlt).symm ▸ hand)
      intro x hx
      change val F (List.ofFn x) (n+j) = true at hx
      rw [(cleanExtensionWires hEF).2 x (n+j) (by omega)] at hx
      exact hc x hx
    · exact hEF.2.2 j hj (by omega) hand

/-- Appending a binary product of available functions preserves every
    old gate. When the product is clean, all newly added ANDs are clean.
    A zero operand costs no new gate, even in the constant-free model. -/
private theorem appendCleanAvailable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D : Circuit) (hD : IsAO2 n D) (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or)
    {f g : (Fin n → Bool) → Bool} (hf : WireAvailable D f) (hg : WireAvailable D g)
    (hc : op = GateOp.and → ∀ x, op.eval [f x,g x] = true → graphFun G ∅ x = true) :
    ∃ E : Circuit, IsAO2 n E ∧ CleanExtension G D E ∧
      E.gates.length ≤ D.gates.length+1 ∧
      ((∀ x, f x = false) ∨ (∀ x, g x = false) → E.gates.length ≤ D.gates.length) ∧
      WireAvailable E (fun x => op.eval [f x,g x]) := by
  rcases hf with hf | ⟨a,ha,hfa⟩
  · rcases hop with rfl | rfl
    · exact ⟨D,hD,cleanExtensionRefl G D,by omega,fun _ => le_rfl,
        Or.inl (fun x => by simp [GateOp.eval,hf x])⟩
    · have he : (fun x => GateOp.or.eval [f x,g x]) = g :=
        funext fun x => by simp [GateOp.eval,hf x]
      exact ⟨D,hD,cleanExtensionRefl G D,by omega,fun _ => le_rfl,he.symm ▸ hg⟩
  · rcases hg with hg | ⟨b,hb,hgb⟩
    · rcases hop with rfl | rfl
      · exact ⟨D,hD,cleanExtensionRefl G D,by omega,fun _ => le_rfl,
          Or.inl (fun x => by simp [GateOp.eval,hg x])⟩
      · have he : (fun x => GateOp.or.eval [f x,g x]) = f :=
          funext fun x => by simp [GateOp.eval,hg x]
        exact ⟨D,hD,cleanExtensionRefl G D,by omega,fun _ => le_rfl,
          he.symm ▸ Or.inr ⟨a,ha,hfa⟩⟩
    · let E := appendBinary D op a b
      obtain ⟨hlen,hE,_,hval⟩ := appendBinary_spec hD hop ha hb
      change E.gates.length = D.gates.length+1 at hlen
      have old (j) (hj : j < D.gates.length) : gateAt E j = gateAt D j := by
        rw [gateAt_eq (by omega : j < E.gates.length),gateAt_eq hj]
        exact List.getElem_append_left hj
      have fresh : gateAt E D.gates.length = ⟨op,[a,b]⟩ := by
        rw [gateAt_eq (by omega : D.gates.length < E.gates.length)]
        simp [E,appendBinary,List.getElem_append_right (le_refl D.gates.length)]
      refine ⟨E,hE,⟨by omega,old,?_⟩,by omega,?_,Or.inr ⟨n+D.gates.length,by omega,?_⟩⟩
      · intro j hj hjD hja
        have he : j = D.gates.length := by omega
        subst j
        rw [fresh] at hja
        intro x hx
        apply hc hja x
        change val E (List.ofFn x) (n+D.gates.length) = true at hx
        rwa [hval x,hfa x,hgb x] at hx
      · rintro (hf | hg)
        · have ht := (hfa _).symm.trans (allTrueWires hD a ha)
          rw [hf _] at ht
          cases ht
        · have ht := (hgb _).symm.trans (allTrueWires hD b hb)
          rw [hg _] at ht
          cases ht
      · intro x
        rw [hval x,hfa x,hgb x]

private lemma falseSuspensionLe {n : ℕ} {C : Circuit} (h : IsAO2 n C) {r : ℕ}
    {W : (Fin n → Bool) → ℕ → Bool} (hW : EvalExcept n C r W)
    (hz : ∀ x, W x (n+r) = false) (x : Fin n → Bool) :
    ∀ w < n+C.gates.length, W x w = true → val C (List.ofFn x) w = true :=
  evalExceptRel h hW (originalEvalExcept h r)
    (R := fun a b => a = true → b = true) (fun _ => id) opMono_imp x
    (by rw [hz x]; intro hf; cases hf)

/-- Unlike the one-junk compiler, this version retains the original
    prefix verbatim and certifies that every appended AND is clean.
    This makes equality of the deletion and repair budgets useful. -/
private theorem compileFalseCleanSuffix {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsAO2 n C) {r : ℕ} (hr : r < C.gates.length)
    (hafter : ∀ j < C.gates.length, r < j → (gateAt C j).op = GateOp.and → BelowF G C j)
    {W : (Fin n → Bool) → ℕ → Bool} (hW : EvalExcept n C r W)
    (hz : ∀ x, W x (n+r) = false)
    (charges : Finset ℕ) (hd : charges ⊆ Finset.range C.gates.length)
    (hcharge : ∀ j ∈ charges, r ≤ j ∧ (j = r ∨
      ∃ w ∈ (gateAt C j).inputs, W (fun _ => true) w = false)) :
    ∃ D : Circuit, IsAO2 n D ∧ D.gates.length+charges.card ≤ C.gates.length ∧
      r ≤ D.gates.length ∧ (∀ j < r, gateAt D j = gateAt C j) ∧
      (∀ j < D.gates.length, r ≤ j → (gateAt D j).op = GateOp.and → BelowF G D j) ∧
      ∀ w < n+C.gates.length, WireAvailable D (fun x => W x w) := by
  classical
  let P : Circuit := ⟨(List.range r).map (gateAt C),0⟩
  have hPl : P.gates.length = r := by simp [P]
  have hPg (j) (hj : j < r) : gateAt P j = gateAt C j := by
    rw [gateAt_eq (by omega : j < P.gates.length)]
    simp [P]
  have hP : IsAO2 n P := by
    refine ⟨?_,?_,?_⟩
    · intro g hg
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hg
      have hj' := List.mem_range.mp hj
      exact h.1 _ (gateAt_mem (by omega))
    · intro j hj w hw
      rw [hPg j (by omega)] at hw
      exact h.2.1 j (by omega) w hw
    · intro g hg
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hg
      have hj' := List.mem_range.mp hj
      exact h.2.2 _ (gateAt_mem (by omega))
  have hWpre (x : Fin n → Bool) (w : ℕ) (hw : w < n+r) :
      W x w = val C (List.ofFn x) w := by
    have he := evalExceptRel h hW (suspendedValue_evalExcept C h r (fun _ => false))
      (R := Eq) (fun _ => rfl) opMono_eq x
      ((hz x).trans (suspendedValue_hole C r (fun _ => false) x).symm) w (by omega)
    exact he.trans (suspendedValue_before C h r hr (fun _ => false) x w hw)
  let budget := fun k => ((Finset.range k).filter fun j => j ∉ charges).card
  have hb0 : budget r = r := by
    have he : (Finset.range r).filter (fun j => j ∉ charges) = Finset.range r := by
      ext j
      simp only [Finset.mem_filter,Finset.mem_range]
      exact ⟨And.left,fun hj => ⟨hj,fun hm => (Nat.not_lt_of_ge (hcharge j hm).1 hj).elim⟩⟩
    simp [budget,he]
  have main : ∀ d, r+d ≤ C.gates.length → ∃ D : Circuit, IsAO2 n D ∧
      CleanExtension G P D ∧ D.gates.length ≤ budget (r+d) ∧
      ∀ w < n+(r+d), WireAvailable D (fun x => W x w) := by
    intro d
    induction d with
    | zero =>
      intro _
      refine ⟨P,hP,cleanExtensionRefl G P,by rw [Nat.add_zero,hb0,hPl],?_⟩
      intro w hw
      have hw' : w < n+r := by omega
      refine Or.inr ⟨w,by omega,fun x => ?_⟩
      exact (val_prefix (n := n) (by simp) (by omega) (by omega) hPg w hw').trans (hWpre x w hw').symm
    | succ d ih =>
      intro hd'
      let k := r+d
      have hk : k < C.gates.length := by dsimp [k]; omega
      have hkr : r ≤ k := by dsimp [k]; omega
      obtain ⟨D,hD,hPD,hlen,havail⟩ := ih (by omega)
      change D.gates.length ≤ budget k at hlen
      have hcount : budget (k+1) = budget k + if k ∈ charges then 0 else 1 := by
        by_cases hm : k ∈ charges
        · simp [budget,Finset.range_add_one,Finset.filter_insert,hm]
        · simp [budget,Finset.range_add_one,Finset.filter_insert,hm]
      have finish (E : Circuit) (hE : IsAO2 n E) (hDE : CleanExtension G D E)
          (hbound : E.gates.length ≤ D.gates.length+1)
          (hfree : k ∈ charges → E.gates.length ≤ D.gates.length)
          (hw : WireAvailable E (fun x => W x (n+k))) :
          ∃ F : Circuit, IsAO2 n F ∧ CleanExtension G P F ∧
            F.gates.length ≤ budget (k+1) ∧
            ∀ w < n+(k+1), WireAvailable F (fun x => W x w) := by
        refine ⟨E,hE,cleanExtensionTrans hPD hDE,?_,?_⟩
        · by_cases hm : k ∈ charges
          · have := hfree hm
            simp only [hm,ite_true,Nat.add_zero] at hcount
            omega
          · simp only [hm,ite_false] at hcount
            omega
        · intro w hwlt
          by_cases he : w = n+k
          · simpa [he] using hw
          · exact wireAvailablePreserved (cleanExtensionWires hDE) (havail w (by omega))
      change ∃ F : Circuit, IsAO2 n F ∧ CleanExtension G P F ∧
        F.gates.length ≤ budget (k+1) ∧
        ∀ w < n+(k+1), WireAvailable F (fun x => W x w)
      by_cases he : k = r
      · exact finish D hD (cleanExtensionRefl G D) (by omega) (fun _ => le_rfl)
          (Or.inl (by simpa [he] using hz))
      obtain ⟨p,q,hpq⟩ := twoOperands h hk
      have hp : p ∈ (gateAt C k).inputs := by simp [hpq]
      have hq : q ∈ (gateAt C k).inputs := by simp [hpq]
      have hP' := havail p (h.2.1 k hk p hp)
      have hQ' := havail q (h.2.1 k hk q hq)
      have hgate (x : Fin n → Bool) :
          W x (n+k) = (gateAt C k).op.eval [W x p,W x q] := by
        rw [hW.2 x k hk he,hpq]
        rfl
      have hc (ha : (gateAt C k).op = GateOp.and) (x : Fin n → Bool)
          (hx : (gateAt C k).op.eval [W x p,W x q] = true) : graphFun G ∅ x = true := by
        apply hafter k hk (by omega) ha x
        apply falseSuspensionLe h hW hz x (n+k) (by omega)
        rwa [hgate x]
      have hfree (hm : k ∈ charges) :
          (∀ x, W x p = false) ∨ (∀ x, W x q = false) := by
        obtain ⟨w,hw,hz'⟩ := (hcharge k hm).2.resolve_left he
        rcases (show w = p ∨ w = q by simpa [hpq] using hw) with rfl | rfl
        · exact Or.inl (wireAvailableFalseOfTop hD hP' hz')
        · exact Or.inr (wireAvailableFalseOfTop hD hQ' hz')
      obtain ⟨E,hE,hDE,hbound,hfree',hw⟩ :=
        appendCleanAvailable G D hD (gateAt C k).op (h.1 _ (gateAt_mem hk)) hP' hQ' hc
      have hf : (fun x => (gateAt C k).op.eval [W x p,W x q]) = fun x => W x (n+k) :=
        funext fun x => (hgate x).symm
      exact finish E hE hDE hbound (fun hm => hfree' (hfree hm)) (hf ▸ hw)
  obtain ⟨D,hD,hPD,hlen,hw⟩ := main (C.gates.length-r) (by omega)
  have he : r+(C.gates.length-r) = C.gates.length := by omega
  rw [he] at hlen hw
  have hc := Finset.card_sdiff_of_subset hd
  have hb : budget C.gates.length = (Finset.range C.gates.length \ charges).card := by
    unfold budget
    rw [Finset.sdiff_eq_filter]
  rw [hb,hc,Finset.card_range] at hlen
  have hcard := Finset.card_le_card hd
  rw [Finset.card_range] at hcard
  have hprelen : r ≤ D.gates.length := by simpa only [hPl] using hPD.1
  refine ⟨D,hD,by omega,hprelen,?_,?_,hw⟩
  · intro j hj
    exact (hPD.2.1 j (by omega)).trans (hPg j hj)
  · intro j hj hge ha
    exact hPD.2.2 j hj (by omega) ha

private def repairProduct {n : ℕ} (W : (Fin n → Bool) → ℕ → Bool)
    (p : ℕ × ℕ) (x : Fin n → Bool) : Bool :=
  W x p.1 && W x p.2

/-- Every repair is a clean conjunction of residual functions already
    available in the suspended compiler. This permits nested providers
    and also includes singleton-edge repairs and ordinary stars. -/
private theorem appendCleanRepairs {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D : Circuit) (hD : IsAO2 n D) (W : (Fin n → Bool) → ℕ → Bool)
    (f : (Fin n → Bool) → Bool) (hf : WireAvailable D f) (ps : List (ℕ × ℕ))
    (hav : ∀ p ∈ ps, WireAvailable D (fun x => W x p.1) ∧ WireAvailable D (fun x => W x p.2))
    (hc : ∀ p ∈ ps, ∀ x, repairProduct W p x = true → graphFun G ∅ x = true) :
    ∃ E : Circuit, IsAO2 n E ∧ CleanExtension G D E ∧
      E.gates.length ≤ D.gates.length+2*ps.length ∧
      (ps ≠ [] → f (fun _ => true) = false →
        E.gates.length+1 ≤ D.gates.length+2*ps.length) ∧
      WireAvailable E (fun x => f x || ps.any (fun p => repairProduct W p x)) := by
  induction ps with
  | nil =>
    exact ⟨D,hD,cleanExtensionRefl G D,by simp,by simp,by simpa using hf⟩
  | cons p ps ih =>
    obtain ⟨B,hB,hDB,hBl,hbonus,hfB⟩ := ih
      (fun t ht => hav t (List.mem_cons_of_mem _ ht))
      (fun t ht => hc t (List.mem_cons_of_mem _ ht))
    obtain ⟨hp,hq⟩ := hav p (by simp)
    have hp' := wireAvailablePreserved (cleanExtensionWires hDB) hp
    have hq' := wireAvailablePreserved (cleanExtensionWires hDB) hq
    obtain ⟨A,hA,hBA,hAl,_,hnew⟩ := appendCleanAvailable G B hB GateOp.and
      (Or.inl rfl) hp' hq' (fun _ x hx => hc p (by simp) x (by simpa [repairProduct,GateOp.eval] using hx))
    have hnew' : WireAvailable A (repairProduct W p) := by
      change WireAvailable A (fun x => W x p.1 && W x p.2)
      simpa [GateOp.eval] using hnew
    let old := fun x => f x || ps.any (fun t => repairProduct W t x)
    have hold : WireAvailable A old := wireAvailablePreserved (cleanExtensionWires hBA) hfB
    obtain ⟨E,hE,hAE,hEl,hfree,hout⟩ := appendCleanAvailable G A hA GateOp.or
      (Or.inr rfl) hold hnew' (fun hn => by cases hn)
    refine ⟨E,hE,cleanExtensionTrans hDB (cleanExtensionTrans hBA hAE),
      by simp only [List.length_cons]; omega,?_,?_⟩
    · intro _ hf0
      simp only [List.length_cons]
      by_cases he : ps = []
      · have hz : old (fun _ => true) = false := by simp [old,he,hf0]
        have hb := hfree (Or.inl (wireAvailableFalseOfTop hA hold hz))
        omega
      · have hb := hbonus he hf0
        omega
    · simpa [old,GateOp.eval,Bool.or_left_comm,Bool.or_comm,Bool.or_assoc] using hout

/-- Any exact same-size clean-suffix repair can be lift-normalized while
    preserving the earlier dirty indices exactly. -/
private theorem descentOfCleanSuffix {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    {r : ℕ} (hrJ : r ∈ junk G C) (hmax : ∀ j ∈ junk G C, j ≤ r)
    (D : Circuit) (hD : IsLeastAO G D) (hlen : D.gates.length = C.gates.length)
    (hpre : ∀ j < r, gateAt D j = gateAt C j)
    (hsuf : ∀ j < D.gates.length, r ≤ j → (gateAt D j).op = GateOp.and → BelowF G D j) :
    ∃ E : Circuit, IsLeastAO G E ∧ IsLiftFixedPoint G E ∧
      E.gates.length = C.gates.length ∧ junk G E = (junk G C).erase r := by
  classical
  have hr := ((memJunkIff G C r).mp hrJ).1
  obtain ⟨E,hE,hfix,hEl,hEp,hEs⟩ :=
    normalizeCleanAndSuffix G C h hl r (by omega) D.gates.length D 0 (by simp)
      hD hlen hpre hsuf (by intro j hj ht; omega)
  refine ⟨E,hE,hfix,hEl,?_⟩
  ext j
  rw [Finset.mem_erase,memJunkIff,memJunkIff]
  by_cases hj : j < r
  · have hv (x : Fin n → Bool) :
        val E (List.ofFn x) (n+j) = val C (List.ofFn x) (n+j) :=
      val_prefix (n := n) (by simp) (by omega) (by omega) hEp _ (by omega)
    have hc : BelowF G E j ↔ BelowF G C j := by
      constructor
      · intro ht x hx
        apply ht x
        change val E (List.ofFn x) (n+j) = true
        rw [hv x]
        exact hx
      · intro ht x hx
        apply ht x
        change val C (List.ofFn x) (n+j) = true
        change val E (List.ofFn x) (n+j) = true at hx
        rwa [hv x] at hx
    rw [hEp j hj,hc,hEl]
    exact ⟨fun ht => ⟨by omega,ht⟩,fun ht => ht.2⟩
  · constructor
    · rintro ⟨hj',ha,hd⟩
      exact (hd (hEs j hj' (by omega) ha)).elim
    · rintro ⟨hne,hj',ha,hd⟩
      have hh := hmax j ((memJunkIff G C j).mpr ⟨hj',ha,hd⟩)
      omega

/-- Main multi-edge descent criterion. False-suspend the last junk,
    cover every lost edge by clean products of residual wires, and
    charge at least the number of gates required to add those products.
    Equality suffices: leastness forces equal size and suffix lifts
    give exactly one fewer dirty AND. No assumptions on earlier junk. -/
theorem lastJunkCleanRepairDescent {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    {r : ℕ} (hrJ : r ∈ junk G C) (hmax : ∀ j ∈ junk G C, j ≤ r)
    {W : (Fin n → Bool) → ℕ → Bool} (hW : EvalExcept n C r W)
    (hz : ∀ x, W x (n+r) = false)
    (charges : Finset ℕ) (hd : charges ⊆ Finset.range C.gates.length)
    (hcharge : ∀ j ∈ charges, r ≤ j ∧ (j = r ∨
      ∃ w ∈ (gateAt C j).inputs, W (fun _ => true) w = false))
    (ps : List (ℕ × ℕ)) (hne : ps ≠ [])
    (hbound : ∀ p ∈ ps, p.1 < n+C.gates.length ∧ p.2 < n+C.gates.length)
    (hc : ∀ p ∈ ps, ∀ x, repairProduct W p x = true → graphFun G ∅ x = true)
    (hcover : ∀ u v, G.Adj u v → W (pairInput u v) C.output = true ∨
      ps.any (fun p => repairProduct W p (pairInput u v)) = true)
    (hbudget : 2*ps.length ≤ charges.card ∨
      (W (fun _ => true) C.output = false ∧ 2*ps.length ≤ charges.card+1)) :
    ∃ E : Circuit, IsLeastAO G E ∧ IsLiftFixedPoint G E ∧
      E.gates.length = C.gates.length ∧ junk G E = (junk G C).erase r := by
  classical
  have hr := ((memJunkIff G C r).mp hrJ).1
  have hafter (j) (hj : j < C.gates.length) (hjr : r < j)
      (ha : (gateAt C j).op = GateOp.and) : BelowF G C j := by
    by_contra hn
    exact (Nat.not_lt_of_ge (hmax j ((memJunkIff G C j).mpr ⟨hj,ha,hn⟩)) hjr)
  have hout := outputLast G C h (by omega : 0 < C.gates.length)
  have hob : C.output < n+C.gates.length := by omega
  obtain ⟨B,hB,hBl,hBr,hBp,hBs,hw⟩ :=
    compileFalseCleanSuffix G C h.1 hr hafter hW hz charges hd hcharge
  obtain ⟨D₀,hD₀,hBD,hDl,hbonus,hres⟩ :=
    appendCleanRepairs G B hB W (fun x => W x C.output) (hw _ hob) ps
      (fun p hp => ⟨hw _ (hbound p hp).1,hw _ (hbound p hp).2⟩) hc
  have hsize : D₀.gates.length ≤ C.gates.length := by
    rcases hbudget with hle | ⟨hf,hle⟩
    · omega
    · have := hbonus hne hf
      omega
  rcases hres with hfalse | ⟨w,_,hv⟩
  · obtain ⟨a,b,hab,hm⟩ := everyGateHasLostEdge G C h hr hW hz
    rcases hcover a b hab with he | he
    · rw [hm] at he
      cases he
    · have hh := hfalse (pairInput a b)
      change (W (pairInput a b) C.output || ps.any (fun p => repairProduct W p (pairInput a b))) = false at hh
      rw [hm,he] at hh
      cases hh
  · let D : Circuit := ⟨D₀.gates,w⟩
    have hD : IsAO2 n D := hD₀
    have hval (x : Fin n → Bool) : circuitFun n D x =
        (W x C.output || ps.any (fun p => repairProduct W p x)) := hv x
    have hcorrect : circuitFun n D = graphFun G ∅ := by
      funext x
      apply Bool.eq_iff_iff.mpr
      constructor
      · intro hx
        rw [hval,Bool.or_eq_true] at hx
        rcases hx with hw' | hp
        · have he := falseSuspensionLe h.1 hW hz x C.output hob hw'
          exact (congrFun h.2.1 x).symm ▸ he
        · obtain ⟨p,hp,ht⟩ := List.any_eq_true.mp hp
          exact hc p hp x ht
      · intro hx
        obtain ⟨a,b,hab,ha,hb⟩ := (graph_true G x).mp hx
        apply circuit_monotone n D (ao_mono hD) (pairInput a b) x ?_ ?_
        · intro z hz'
          rcases (show z = a ∨ z = b by simpa [pairInput] using hz') with rfl | rfl
          · exact ha
          · exact hb
        · change circuitFun n D (pairInput a b) = true
          rw [hval,Bool.or_eq_true]
          exact hcover a b hab
    have hmin := h.2.2 D hD hcorrect
    change C.gates.length ≤ D₀.gates.length at hmin
    have hlen : D.gates.length = C.gates.length := by change D₀.gates.length = _; omega
    have hleast : IsLeastAO G D := ⟨hD,hcorrect,fun F hF hf => by
      have hm := h.2.2 F hF hf
      change D.gates.length ≤ F.gates.length
      change C.gates.length ≤ F.gates.length at hm
      omega⟩
    apply descentOfCleanSuffix G C h hl hrJ hmax D hleast hlen
    · intro j hj
      exact (hBD.2.1 j (by omega)).trans (hBp j hj)
    · intro j hj hge hja
      by_cases hlt : j < B.gates.length
      · have hb := hBs j hlt hge ((hBD.2.1 j hlt).symm ▸ hja)
        intro x hx
        change val D₀ (List.ofFn x) (n+j) = true at hx
        rw [(cleanExtensionWires hBD).2 x (n+j) (by omega)] at hx
        exact hb x hx
      · exact hBD.2.2 j hj (by omega) hja

/-- A concrete application: two or more pivotal edges can be covered by
    one clean residual product. The last junk and any immediate reader
    pay for it. There is no singleton-edge premise. -/
theorem lastJunkOneProductDescent {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    {r i : ℕ} (hrJ : r ∈ junk G C) (hmax : ∀ j ∈ junk G C, j ≤ r)
    (hi : i < C.gates.length) (hir : n+r ∈ (gateAt C i).inputs)
    {W : (Fin n → Bool) → ℕ → Bool} (hW : EvalExcept n C r W)
    (hz : ∀ x, W x (n+r) = false)
    (p q : ℕ) (hp : p < n+C.gates.length) (hq : q < n+C.gates.length)
    (hc : ∀ x, W x p = true → W x q = true → graphFun G ∅ x = true)
    (hcover : ∀ u v, G.Adj u v → W (pairInput u v) C.output = false →
      W (pairInput u v) p = true ∧ W (pairInput u v) q = true) :
    ∃ E : Circuit, IsLeastAO G E ∧ IsLiftFixedPoint G E ∧
      E.gates.length = C.gates.length ∧ junk G E = (junk G C).erase r := by
  classical
  have hr := ((memJunkIff G C r).mp hrJ).1
  have hri : r < i := by have := h.1.2.1 i hi _ hir; omega
  apply lastJunkCleanRepairDescent G C h hl hrJ hmax hW hz {r,i}
    (by intro j hj; rcases (show j = r ∨ j = i by simpa using hj) with rfl | rfl <;>
      exact Finset.mem_range.mpr (by omega)) ?_ [(p,q)] (by simp) ?_ ?_ ?_ ?_
  · intro j hj
    rcases (show j = r ∨ j = i by simpa using hj) with rfl | rfl
    · exact ⟨le_rfl,Or.inl rfl⟩
    · exact ⟨by omega,Or.inr ⟨n+r,hir,hz _⟩⟩
  · intro t ht
    have he : t = (p,q) := by simpa using ht
    subst t
    exact ⟨hp,hq⟩
  · intro t ht x hx
    have he : t = (p,q) := by simpa using ht
    subst t
    have hpair : W x p = true ∧ W x q = true := by simpa [repairProduct] using hx
    obtain ⟨hpx,hqx⟩ := hpair
    exact hc x hpx hqx
  · intro u v huv
    cases he : W (pairInput u v) C.output
    · exact Or.inr (by simpa [repairProduct] using hcover u v huv he)
    · exact Or.inl rfl
  · exact Or.inl (by simp [hri.ne])

#print axioms lastJunkCleanRepairDescent
#print axioms lastJunkOneProductDescent


/-! Multi-hole suspension with exclusive-cone accounting. Unlike
    prefix-preserving descent, a strict repair may discard earlier junk. -/

def EvalHoles {n : ℕ} (C : Circuit) (holes : Finset ℕ)
    (W : (Fin n → Bool) → ℕ → Bool) : Prop :=
  (∀ x (v : Fin n), W x v.val = x v) ∧
  (∀ x j, j < C.gates.length → j ∈ holes → W x (n+j) = false) ∧
  ∀ x j, j < C.gates.length → j ∉ holes →
    W x (n+j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (W x))

private def holesValue {n : ℕ} (C : Circuit) (holes : Finset ℕ)
    (x : Fin n → Bool) (w : ℕ) : Bool :=
  if hw : w < n then x ⟨w,hw⟩
  else if w-n ∈ holes then false
  else (gateAt C (w-n)).op.eval ((gateAt C (w-n)).inputs.attach.map fun v =>
    if _hv : v.val < w then holesValue C holes x v.val else false)
termination_by w

theorem existsEvalHoles {n : ℕ} (C : Circuit) (h : IsAO2 n C) (holes : Finset ℕ) :
    ∃ W : (Fin n → Bool) → ℕ → Bool, EvalHoles C holes W := by
  refine ⟨holesValue C holes,?_,?_,?_⟩
  · intro x v
    rw [holesValue,dite_eq_left v.isLt]
  · intro x j _ hj
    rw [holesValue,dite_eq_right (by omega),Nat.add_sub_cancel_left,ite_eq_left hj]
  · intro x j hj hn
    rw [holesValue,dite_eq_right (by omega),Nat.add_sub_cancel_left,ite_eq_right hn]
    congr 1
    conv => rhs; rw [← List.attach_map_val]
    apply List.map_congr_left
    intro v _
    rw [dite_eq_left (h.2.1 j hj v.val v.property)]

/-- All selected zero fillings are below the original evaluation. The
    valuation itself is monotone, so testing the all-true input detects
    functions that are identically false. -/
private theorem holesCompare {n : ℕ} {C : Circuit} (h : IsAO2 n C)
    {holes : Finset ℕ} {W : (Fin n → Bool) → ℕ → Bool}
    (hW : EvalHoles C holes W) (x : Fin n → Bool) :
    ∀ w < n+C.gates.length,
      (W x w = true → val C (List.ofFn x) w = true) ∧
      (W x w = true → W (fun _ => true) w = true) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hn : w < n
    · let v : Fin n := ⟨w,hn⟩
      have he : val C (List.ofFn x) w = x v := (originalEvalExcept h 0).1 x v
      rw [hW.1 x v,hW.1 (fun _ => true) v,he]
      exact ⟨id,fun _ => rfl⟩
    obtain ⟨j,rfl⟩ : ∃ j, w = n+j := ⟨w-n,by omega⟩
    have hj : j < C.gates.length := by omega
    by_cases hm : j ∈ holes
    · rw [hW.2.1 x j hj hm]
      constructor <;> intro hf <;> cases hf
    have he := (originalEvalExcept h C.gates.length).2 x j hj (by omega)
    dsimp only at he
    rw [hW.2.2 x j hj hm,hW.2.2 (fun _ => true) j hj hm,he]
    constructor
    · apply opMono_imp _ (h.1 _ (gateAt_mem hj))
      intro p hp
      have hb := h.2.1 j hj p hp
      exact (ih p hb (by omega)).1
    · apply opMono_imp _ (h.1 _ (gateAt_mem hj))
      intro p hp
      have hb := h.2.1 j hj p hp
      exact (ih p hb (by omega)).2

private lemma holesZero {n : ℕ} {C : Circuit} (h : IsAO2 n C)
    {holes : Finset ℕ} {W : (Fin n → Bool) → ℕ → Bool}
    (hW : EvalHoles C holes W) {w : ℕ} (hw : w < n+C.gates.length)
    (hz : W (fun _ => true) w = false) : ∀ x, W x w = false := by
  intro x
  cases he : W x w
  · rfl
  · have ht := (holesCompare h hW x w hw).2 he
    rw [hz] at ht
    cases ht

/-- A selected residual compiler. Only needed, nonzero functions must
    be realized; a zero operand is free and unneeded nonzero cones may
    be discarded. A gate is paid for only if selected and not simplified.
    The finite paid set need not be restricted to a suffix. -/
theorem compileExclusiveHoles {n : ℕ} (C : Circuit) (h : IsAO2 n C)
    {holes : Finset ℕ} {W : (Fin n → Bool) → ℕ → Bool}
    (hW : EvalHoles C holes W) (need : ℕ → Prop) (paid : Finset ℕ)
    (hclosed : ∀ j < C.gates.length, need (n+j) →
      W (fun _ => true) (n+j) = true → ∀ w ∈ (gateAt C j).inputs,
        w < n ∨ need w ∨ W (fun _ => true) w = false)
    (hpay : ∀ j < C.gates.length, need (n+j) →
      W (fun _ => true) (n+j) = true → j ∉ paid →
        ∃ w ∈ (gateAt C j).inputs, W (fun _ => true) w = false) :
    ∃ D : Circuit, IsAO2 n D ∧ D.gates.length ≤ paid.card ∧
      ∀ w < n+C.gates.length, w < n ∨ need w ∨ W (fun _ => true) w = false →
        WireAvailable D (fun x => W x w) := by
  classical
  let budget := fun k => ((Finset.range k).filter fun j => j ∈ paid).card
  let requested := fun w => w < n ∨ need w ∨ W (fun _ => true) w = false
  have main : ∀ k ≤ C.gates.length, ∃ D : Circuit, IsAO2 n D ∧
      D.gates.length ≤ budget k ∧
      ∀ w < n+k, requested w → WireAvailable D (fun x => W x w) := by
    intro k
    induction k with
    | zero =>
      intro _
      let D : Circuit := ⟨[],0⟩
      have hD : IsAO2 n D := by
        refine ⟨fun g hg => ?_,fun j hj => ?_,fun g hg => ?_⟩ <;> simp [D] at *
      refine ⟨D,hD,by simp [D],?_⟩
      intro w hw _
      have hn : w < n := by omega
      let v : Fin n := ⟨w,hn⟩
      refine Or.inr ⟨w,by simpa [D] using hn,?_⟩
      intro x
      exact ((originalEvalExcept hD 0).1 x v).trans (hW.1 x v).symm
    | succ k ih =>
      intro hk
      obtain ⟨D,hD,hlen,havail⟩ := ih (by omega)
      have hj : k < C.gates.length := by omega
      have hcount : budget (k+1) = budget k + if k ∈ paid then 1 else 0 := by
        by_cases hm : k ∈ paid
        · simp [budget,Finset.range_add_one,Finset.filter_insert,hm]
        · simp [budget,Finset.range_add_one,Finset.filter_insert,hm]
      have finish (E : Circuit) (hE : IsAO2 n E) (hkeep : PreservesWires n D E)
          (hbound : E.gates.length ≤ D.gates.length+1)
          (hfree : k ∉ paid → E.gates.length ≤ D.gates.length)
          (hw : requested (n+k) → WireAvailable E (fun x => W x (n+k))) :
          ∃ F : Circuit, IsAO2 n F ∧ F.gates.length ≤ budget (k+1) ∧
            ∀ w < n+(k+1), requested w → WireAvailable F (fun x => W x w) := by
        refine ⟨E,hE,?_,?_⟩
        · by_cases hm : k ∈ paid
          · simp only [hm,ite_true] at hcount
            omega
          · have := hfree hm
            simp only [hm,ite_false,Nat.add_zero] at hcount
            omega
        · intro w hwlt hn
          by_cases he : w = n+k
          · subst w
            exact hw hn
          · exact wireAvailablePreserved hkeep (havail w (by omega) hn)
      cases htop : W (fun _ => true) (n+k)
      · exact finish D hD ⟨le_rfl,fun _ _ _ => rfl⟩ (by omega) (fun _ => le_rfl)
          (fun _ => Or.inl (holesZero h hW (by omega) htop))
      by_cases hn : need (n+k)
      · have hnot : k ∉ holes := by
          intro hm
          have hh := hW.2.1 (fun _ => true) k hj hm
          rw [htop] at hh
          cases hh
        obtain ⟨p,q,hpq⟩ := twoOperands h hj
        have hp : p ∈ (gateAt C k).inputs := by simp [hpq]
        have hq : q ∈ (gateAt C k).inputs := by simp [hpq]
        have hP := havail p (h.2.1 k hj p hp) (hclosed k hj hn htop p hp)
        have hQ := havail q (h.2.1 k hj q hq) (hclosed k hj hn htop q hq)
        have hfree (hm : k ∉ paid) :
            (∀ x, W x p = false) ∨ (∀ x, W x q = false) := by
          obtain ⟨w,hw,hz⟩ := hpay k hj hn htop hm
          rcases (show w = p ∨ w = q by simpa [hpq] using hw) with rfl | rfl
          · exact Or.inl (wireAvailableFalseOfTop hD hP hz)
          · exact Or.inr (wireAvailableFalseOfTop hD hQ hz)
        rcases h.1 _ (gateAt_mem hj) with ha | ho
        · obtain ⟨E,hE,hkeep,hbound,hfree',hw⟩ := appendAvailableAnd D hD hP hQ
          have he : (fun x => W x p && W x q) = fun x => W x (n+k) := by
            funext x
            simpa [ha,hpq,GateOp.eval] using (hW.2.2 x k hj hnot).symm
          exact finish E hE hkeep hbound (fun hm => hfree' (hfree hm)) (fun _ => he ▸ hw)
        · obtain ⟨E,hE,hkeep,hbound,hfree',hw⟩ := appendAvailableOr D hD hP hQ
          have he : (fun x => W x p || W x q) = fun x => W x (n+k) := by
            funext x
            simpa [ho,hpq,GateOp.eval] using (hW.2.2 x k hj hnot).symm
          exact finish E hE hkeep hbound (fun hm => hfree' (hfree hm)) (fun _ => he ▸ hw)
      · exact finish D hD ⟨le_rfl,fun _ _ _ => rfl⟩ (by omega) (fun _ => le_rfl)
          (fun hw => by
            rcases hw with hw | hw | hw
            · omega
            · exact (hn hw).elim
            · rw [htop] at hw
              cases hw)
  obtain ⟨D,hD,hlen,hw⟩ := main C.gates.length le_rfl
  have hb : ((Finset.range C.gates.length).filter fun j => j ∈ paid) ⊆ paid := by
    intro j hj
    exact (Finset.mem_filter.mp hj).2
  exact ⟨D,hD,hlen.trans (Finset.card_le_card hb),hw⟩

/-- A global strict budget excludes a least circuit. All suspended
    holes can be selected simultaneously; the unused true-valued gates
    need not be retained, in contrast to the earlier suffix compiler. -/
theorem noExclusiveConeRepair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C)
    (hpos : 0 < C.gates.length)
    {holes : Finset ℕ} {W : (Fin n → Bool) → ℕ → Bool}
    (hW : EvalHoles C holes W) (need : ℕ → Prop) (paid : Finset ℕ)
    (hclosed : ∀ j < C.gates.length, need (n+j) →
      W (fun _ => true) (n+j) = true → ∀ w ∈ (gateAt C j).inputs,
        w < n ∨ need w ∨ W (fun _ => true) w = false)
    (hpay : ∀ j < C.gates.length, need (n+j) →
      W (fun _ => true) (n+j) = true → j ∉ paid →
        ∃ w ∈ (gateAt C j).inputs, W (fun _ => true) w = false)
    (houtNeed : C.output < n ∨ need C.output ∨ W (fun _ => true) C.output = false)
    (ps : List (ℕ × ℕ))
    (hbound : ∀ p ∈ ps, p.1 < n+C.gates.length ∧ p.2 < n+C.gates.length)
    (hneed : ∀ p ∈ ps,
      (p.1 < n ∨ need p.1 ∨ W (fun _ => true) p.1 = false) ∧
      (p.2 < n ∨ need p.2 ∨ W (fun _ => true) p.2 = false))
    (hc : ∀ p ∈ ps, ∀ x, repairProduct W p x = true → graphFun G ∅ x = true)
    (hcover : ∀ u v, G.Adj u v → W (pairInput u v) C.output = true ∨
      ps.any (fun p => repairProduct W p (pairInput u v)) = true)
    (hbudget : paid.card+2*ps.length < C.gates.length ∨
      (ps ≠ [] ∧ W (fun _ => true) C.output = false ∧
        paid.card+2*ps.length ≤ C.gates.length)) : False := by
  have hout := outputLast G C h hpos
  have hob : C.output < n+C.gates.length := by omega
  obtain ⟨B,hB,hBl,hw⟩ := compileExclusiveHoles C h.1 hW need paid hclosed hpay
  obtain ⟨D₀,hD₀,_,hDl,hbonus,hres⟩ :=
    appendCleanRepairs G B hB W (fun x => W x C.output) (hw _ hob houtNeed) ps
      (fun p hp => ⟨hw _ (hbound p hp).1 (hneed p hp).1,
        hw _ (hbound p hp).2 (hneed p hp).2⟩) hc
  have hsize : D₀.gates.length < C.gates.length := by
    rcases hbudget with hlt | ⟨hne,hf,hle⟩
    · omega
    · have := hbonus hne hf
      omega
  rcases hres with hfalse | ⟨w,_,hv⟩
  · have hno (a b : Fin n) (hab : G.Adj a b) : False := by
      have hh := hfalse (pairInput a b)
      change (W (pairInput a b) C.output || ps.any (fun p => repairProduct W p (pairInput a b))) = false at hh
      have ht : (W (pairInput a b) C.output || ps.any (fun p => repairProduct W p (pairInput a b))) = true := by
        rw [Bool.or_eq_true]
        exact hcover a b hab
      rw [ht] at hh
      cases hh
    have he := emptyGraphNoGates G C h hno
    omega
  · let D : Circuit := ⟨D₀.gates,w⟩
    have hD : IsAO2 n D := hD₀
    have hval (x : Fin n → Bool) : circuitFun n D x =
        (W x C.output || ps.any (fun p => repairProduct W p x)) := hv x
    have hcorrect : circuitFun n D = graphFun G ∅ := by
      funext x
      apply Bool.eq_iff_iff.mpr
      constructor
      · intro hx
        rw [hval,Bool.or_eq_true] at hx
        rcases hx with hq | hp
        · have he := (holesCompare h.1 hW x C.output hob).1 hq
          exact (congrFun h.2.1 x).symm ▸ he
        · obtain ⟨p,hp,ht⟩ := List.any_eq_true.mp hp
          exact hc p hp x ht
      · intro hx
        obtain ⟨a,b,hab,ha,hb⟩ := (graph_true G x).mp hx
        apply circuit_monotone n D (ao_mono hD) (pairInput a b) x ?_ ?_
        · intro z hz
          rcases (show z = a ∨ z = b by simpa [pairInput] using hz) with rfl | rfl
          · exact ha
          · exact hb
        · change circuitFun n D (pairInput a b) = true
          rw [hval,Bool.or_eq_true]
          exact hcover a b hab
    have hm := h.2.2 D hD hcorrect
    change C.gates.length ≤ D₀.gates.length at hm
    omega

/-- Concrete raw-edge version: keep only the residual output cone;
    each uncovered edge costs one AND and at most one collector OR.
    The inequality is a necessary global constraint on every least
    circuit, not merely on the last dirty gate or its reader count. -/
theorem exclusiveConeRawEdgeLowerBound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C)
    (hpos : 0 < C.gates.length)
    {holes : Finset ℕ} {W : (Fin n → Bool) → ℕ → Bool}
    (hW : EvalHoles C holes W) (need : ℕ → Prop) (paid : Finset ℕ)
    (hclosed : ∀ j < C.gates.length, need (n+j) →
      W (fun _ => true) (n+j) = true → ∀ w ∈ (gateAt C j).inputs,
        w < n ∨ need w ∨ W (fun _ => true) w = false)
    (hpay : ∀ j < C.gates.length, need (n+j) →
      W (fun _ => true) (n+j) = true → j ∉ paid →
        ∃ w ∈ (gateAt C j).inputs, W (fun _ => true) w = false)
    (houtNeed : C.output < n ∨ need C.output ∨ W (fun _ => true) C.output = false)
    (es : List (Fin n × Fin n))
    (hadj : ∀ e ∈ es, G.Adj e.1 e.2)
    (hcover : ∀ u v, G.Adj u v → W (pairInput u v) C.output = false →
      ∃ e ∈ es, pairInput e.1 e.2 = pairInput u v) :
    C.gates.length ≤ paid.card+2*es.length ∧
      (es ≠ [] → W (fun _ => true) C.output = false →
        C.gates.length < paid.card+2*es.length) := by
  classical
  let ps := es.map (fun e => (e.1.val,e.2.val))
  have hplen : ps.length = es.length := by simp [ps]
  have hbound (p) (hp : p ∈ ps) : p.1 < n+C.gates.length ∧ p.2 < n+C.gates.length := by
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hp
    have h1 := e.1.isLt
    have h2 := e.2.isLt
    exact ⟨by omega,by omega⟩
  have hneed (p) (hp : p ∈ ps) :
      (p.1 < n ∨ need p.1 ∨ W (fun _ => true) p.1 = false) ∧
      (p.2 < n ∨ need p.2 ∨ W (fun _ => true) p.2 = false) := by
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hp
    exact ⟨Or.inl e.1.isLt,Or.inl e.2.isLt⟩
  have hc (p) (hp : p ∈ ps) (x : Fin n → Bool)
      (ht : repairProduct W p x = true) : graphFun G ∅ x = true := by
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hp
    have hh : x e.1 = true ∧ x e.2 = true := by
      simpa [repairProduct,hW.1 x e.1,hW.1 x e.2] using ht
    exact (graph_true G x).mpr ⟨e.1,e.2,hadj e he,hh.1,hh.2⟩
  have hcov (u v : Fin n) (huv : G.Adj u v) :
      W (pairInput u v) C.output = true ∨
        ps.any (fun p => repairProduct W p (pairInput u v)) = true := by
    cases he : W (pairInput u v) C.output
    · obtain ⟨e,he',heq⟩ := hcover u v huv he
      refine Or.inr (List.any_eq_true.mpr ⟨(e.1.val,e.2.val),List.mem_map.mpr ⟨e,he',rfl⟩,?_⟩)
      rw [← heq]
      simp [repairProduct,hW.1 (pairInput e.1 e.2) e.1,
        hW.1 (pairInput e.1 e.2) e.2,pairInput]
    · exact Or.inl rfl
  have no := noExclusiveConeRepair G C h hpos hW need paid hclosed hpay houtNeed ps hbound hneed hc hcov
  constructor
  · by_contra hn
    exact no (Or.inl (by omega))
  · intro hne hf
    by_contra hn
    have hpne : ps ≠ [] := by
      intro he
      have hz : ps.length = 0 := by simp [he]
      exact hne (List.length_eq_zero_iff.mp (hplen.symm.trans hz))
    exact no (Or.inr ⟨hpne,hf,by omega⟩)

#print axioms existsEvalHoles
#print axioms compileExclusiveHoles
#print axioms noExclusiveConeRepair
#print axioms exclusiveConeRawEdgeLowerBound

end ResearchVerification.OneJunkErase
