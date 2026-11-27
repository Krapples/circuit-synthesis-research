/-
First-gate facts for minimal free-NOT AIGs (2026-11-26).

The certificate recursion of `sat-search/results/mid_not_16102/aig8_recursion_proof.md` needs these facts
about a circuit that is minimal in size and, among those, has the fewest readers of its first gate:

* gates are indexed earliest first (`gt`), and every operand reads an earlier wire (`WF`);
* the first gate reads two distinct inputs `x_i^ai`, `x_j^aj`, and no reader of it reads `x_i` or `x_j`
  (otherwise that reader can read the inputs directly, which leaves the first gate with fewer readers);
* restricting an input deletes every gate in a cascade set; `cascade_ge` counts explicit sets.
-/
import CircuitLemmas.GateElim

namespace CircuitLemmas.GateElim.FirstGate

open CircuitLemmas.GateElim

def dflt : Gate := ⟨.const false, .const false⟩

/-- Gate `k`, counting from the earliest. -/
def gt (rgs : List Gate) (k : ℕ) : Gate := rgs.reverse.getD k dflt

/-- The gates before gate `k` (latest first). -/
def earl (rgs : List Gate) (k : ℕ) : List Gate := (rgs.reverse.take k).reverse

/-- The gates after gate `k` (latest first). -/
def late (rgs : List Gate) (k : ℕ) : List Gate := (rgs.reverse.drop (k + 1)).reverse

/-- Gate `g` reads wire `u`. -/
def Rd (g : Gate) (u : ℕ) : Prop := g.a.Reads u ∨ g.b.Reads u

theorem gt_eq (rgs : List Gate) (k : ℕ) (hk : k < rgs.length) :
    gt rgs k = rgs.reverse[k]'(by simpa using hk) := by
  simp [gt, List.getD_eq_getElem?_getD, hk]

theorem split (rgs : List Gate) (k : ℕ) (hk : k < rgs.length) :
    rgs = late rgs k ++ gt rgs k :: earl rgs k := by
  have hk' : k < rgs.reverse.length := by simpa using hk
  have h1 : rgs.reverse = rgs.reverse.take k ++ rgs.reverse[k] :: rgs.reverse.drop (k + 1) := by
    rw [List.getElem_cons_drop, List.take_append_drop]
  rw [gt_eq rgs k hk]
  conv_lhs => rw [← List.reverse_reverse rgs, h1]
  simp [late, earl]

theorem earl_length (rgs : List Gate) (k : ℕ) (hk : k ≤ rgs.length) : (earl rgs k).length = k := by
  simp [earl]; omega

theorem mem_late (rgs : List Gate) (k : ℕ) (g : Gate) (hg : g ∈ late rgs k) :
    ∃ k', k < k' ∧ k' < rgs.length ∧ gt rgs k' = g := by
  simp only [late, List.mem_reverse] at hg
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hg
  simp only [List.length_drop, List.length_reverse] at hi
  refine ⟨k + 1 + i, by omega, by omega, ?_⟩
  rw [gt_eq rgs _ (by omega)]
  simp [List.getElem_drop]

/-! ## Wire values -/

theorem val_cons_at (n : ℕ) (x : ℕ → Bool) (later : List Gate) (g : Gate) (e : List Gate) :
    val n x (later ++ g :: e) (n + e.length) = g.eval (val n x e) := by
  rw [val_append_lt n x (g :: e) later _ (by simp)]
  simp [val]

theorem val_gate (n : ℕ) (x : ℕ → Bool) (rgs : List Gate) (k : ℕ) (hk : k < rgs.length) :
    val n x rgs (n + k) = (gt rgs k).eval (val n x (earl rgs k)) := by
  have h := val_cons_at n x (late rgs k) (gt rgs k) (earl rgs k)
  rw [← split rgs k hk, earl_length rgs k hk.le] at h
  exact h

theorem val_earl (n : ℕ) (x : ℕ → Bool) (rgs : List Gate) (k : ℕ) (hk : k < rgs.length) (u : ℕ)
    (hu : u < n + k) : val n x (earl rgs k) u = val n x rgs u := by
  have hl := earl_length rgs k hk.le
  conv_rhs => rw [split rgs k hk]
  rw [val_append_lt n x _ _ u (by simp only [List.length_cons]; omega)]
  simp only [val]
  rw [if_neg (by omega)]

/-- Every operand of gate `k` reads an earlier wire. -/
def WF (n : ℕ) (rgs : List Gate) : Prop := ∀ k < rgs.length, ∀ u, Rd (gt rgs k) u → u < n + k

theorem ref_congr (r : Ref) (B : ℕ) (hr : ∀ u, r.Reads u → u < B) (v v' : ℕ → Bool)
    (h : ∀ u < B, v u = v' u) : r.eval v = r.eval v' := by
  cases r with
  | const c => rfl
  | wire w neg => simp [Ref.eval, h w (hr w (by simp [Ref.Reads]))]

theorem val_gate_wf (n : ℕ) (x : ℕ → Bool) (rgs : List Gate) (hW : WF n rgs) (k : ℕ)
    (hk : k < rgs.length) : val n x rgs (n + k) = (gt rgs k).eval (val n x rgs) := by
  rw [val_gate n x rgs k hk]
  unfold Gate.eval
  rw [ref_congr _ (n + k) (fun u hu => hW k hk u (Or.inl hu)) _ (val n x rgs)
      (fun u hu => val_earl n x rgs k hk u hu),
    ref_congr _ (n + k) (fun u hu => hW k hk u (Or.inr hu)) _ (val n x rgs)
      (fun u hu => val_earl n x rgs k hk u hu)]

/-! ## Counting gates by position -/

section count
open Classical

theorem card_eq (P : Gate → List Gate → Prop) (F : List Gate → ℕ) (h0 : F [] = 0)
    (hs : ∀ g r, F (g :: r) = (if P g r then 1 else 0) + F r) :
    ∀ rgs : List Gate, F rgs = ((Finset.range rgs.length).filter fun k => P (gt rgs k) (earl rgs k)).card
  | [] => by simp [h0]
  | g :: r => by
      rw [hs, card_eq P F h0 hs r]
      have hg : gt (g :: r) r.length = g := by
        rw [gt_eq _ _ (by simp)]; simp
      have he : earl (g :: r) r.length = r := by simp [earl]
      have hlt : ∀ k < r.length, gt (g :: r) k = gt r k ∧ earl (g :: r) k = earl r k := by
        intro k hk
        refine ⟨?_, ?_⟩
        · rw [gt_eq _ _ (by simp; omega), gt_eq _ _ hk]
          simp only [List.reverse_cons]
          rw [List.getElem_append_left (by simpa using hk)]
        · simp [earl, List.take_append_of_le_length (show k ≤ r.reverse.length by simp; omega)]
      have hfil : ((Finset.range r.length).filter fun k => P (gt (g :: r) k) (earl (g :: r) k)) =
          (Finset.range r.length).filter fun k => P (gt r k) (earl r k) := by
        refine Finset.filter_congr fun k hk => ?_
        obtain ⟨h1, h2⟩ := hlt k (Finset.mem_range.1 hk)
        rw [h1, h2]
      simp only [List.length_cons, Finset.range_add_one, Finset.filter_insert, hg, he, hfil]
      split_ifs with hP
      · rw [Finset.card_insert_of_notMem (by simp)]; omega
      · omega

theorem readers_eq (z : ℕ) (rgs : List Gate) :
    readers z rgs = ((Finset.range rgs.length).filter fun k => Rd (gt rgs k) z).card := by
  refine card_eq (fun g _ => Rd g z) (readers z) (by simp [readers]) (fun g r => ?_) rgs
  simp only [readers, List.filter_cons, Rd]
  split_ifs with h1 h2 h2 <;> simp_all <;> omega

theorem cascade_eq (n z : ℕ) (b : Bool) (rgs : List Gate) :
    cascade n z b rgs = ((Finset.range rgs.length).filter fun k =>
      (gt rgs k).a.ReadsConst n z b (earl rgs k) ∨ (gt rgs k).b.ReadsConst n z b (earl rgs k)).card := by
  rw [card_eq (fun g r => g.a.ReadsConst n z b r ∨ g.b.ReadsConst n z b r) (cascade n z b) rfl
    (fun g r => by
      simp only [cascade]
      by_cases h : g.a.ReadsConst n z b r ∨ g.b.ReadsConst n z b r <;> simp [h]) rgs]
  congr 1
  exact Finset.filter_congr_decidable _ _ _

/-- Readers of `z` form a set of positions. -/
theorem card_le_readers (z : ℕ) (rgs : List Gate) (K : Finset ℕ)
    (hK : ∀ k ∈ K, k < rgs.length ∧ Rd (gt rgs k) z) : K.card ≤ readers z rgs := by
  rw [readers_eq]
  exact Finset.card_le_card fun k hk => by simp [hK k hk]

theorem readers_le_card (z : ℕ) (rgs : List Gate) (K : Finset ℕ)
    (hK : ∀ k < rgs.length, Rd (gt rgs k) z → k ∈ K) : readers z rgs ≤ K.card := by
  rw [readers_eq]
  exact Finset.card_le_card fun k hk => by simp at hk; exact hK k hk.1 hk.2

/-- A set of gates, each with an operand that is constant under `z := b`, is deleted by the restriction. -/
theorem cascade_ge (n z : ℕ) (b : Bool) (rgs : List Gate) (hW : WF n rgs) (K : Finset ℕ)
    (hK : ∀ k ∈ K, k < rgs.length ∧ ∃ u, Rd (gt rgs k) u ∧ ConstUnder n z b rgs u) :
    K.card ≤ cascade n z b rgs := by
  rw [cascade_eq]
  refine Finset.card_le_card fun k hk => ?_
  obtain ⟨hkl, u, hu, c, hc⟩ := hK k hk
  have hc' : ConstUnder n z b (earl rgs k) u :=
    ⟨c, fun x => by rw [val_earl n _ rgs k hkl u (hW k hkl u hu)]; exact hc x⟩
  simp only [Finset.mem_filter, Finset.mem_range]
  refine ⟨hkl, ?_⟩
  rcases hu with h | h
  · left
    cases ha : (gt rgs k).a with
    | const c => simp [ha, Ref.Reads] at h
    | wire w neg =>
        rw [ha] at h; simp only [Ref.Reads] at h; subst h
        simpa [Ref.ReadsConst] using hc'
  · right
    cases ha : (gt rgs k).b with
    | const c => simp [ha, Ref.Reads] at h
    | wire w neg =>
        rw [ha] at h; simp only [Ref.Reads] at h; subst h
        simpa [Ref.ReadsConst] using hc'

end count

/-! ## Constant wires under a restriction -/

theorem cu_input (n z : ℕ) (b : Bool) (rgs : List Gate) (hz : z < n) : ConstUnder n z b rgs z :=
  ⟨b, fun x => by rw [val_input n _ rgs z hz, upd_same]⟩

theorem ref_cu (n z : ℕ) (b : Bool) (rgs : List Gate) (r : Ref)
    (h : ∀ u neg, r = .wire u neg → ConstUnder n z b rgs u) :
    ∃ c, ∀ x, r.eval (val n (upd x z b) rgs) = c := by
  cases r with
  | const c => exact ⟨c, fun _ => rfl⟩
  | wire u neg =>
      obtain ⟨c, hc⟩ := h u neg rfl
      exact ⟨Bool.xor c neg, fun x => by simp [Ref.eval, hc]⟩

/-- A gate whose operands are all constant under the restriction is constant. -/
theorem cu_gate (n z : ℕ) (b : Bool) (rgs : List Gate) (hW : WF n rgs) (k : ℕ) (hk : k < rgs.length)
    (ha : ∀ u neg, (gt rgs k).a = .wire u neg → ConstUnder n z b rgs u)
    (hb : ∀ u neg, (gt rgs k).b = .wire u neg → ConstUnder n z b rgs u) :
    ConstUnder n z b rgs (n + k) := by
  obtain ⟨ca, hca⟩ := ref_cu n z b rgs _ ha
  obtain ⟨cb, hcb⟩ := ref_cu n z b rgs _ hb
  exact ⟨ca && cb, fun x => by rw [val_gate_wf n _ rgs hW k hk]; simp [Gate.eval, hca, hcb]⟩

/-- A gate with an operand literal that the restriction makes false is constant. -/
theorem cu_ctrl (n z : ℕ) (b : Bool) (rgs : List Gate) (hW : WF n rgs) (k : ℕ) (hk : k < rgs.length)
    (u : ℕ) (neg : Bool) (hr : (gt rgs k).a = .wire u neg ∨ (gt rgs k).b = .wire u neg)
    (hc : ∀ x, val n (upd x z b) rgs u = neg) : ConstUnder n z b rgs (n + k) := by
  refine ⟨false, fun x => ?_⟩
  rw [val_gate_wf n _ rgs hW k hk]
  rcases hr with h | h <;> simp [Gate.eval, h, Ref.eval, hc]

/-! ## Minimal circuits -/

def IsMin (n : ℕ) (f : (ℕ → Bool) → Bool) (C : Circuit) : Prop :=
  C.n = n ∧ (∀ x, C.eval x = f x) ∧ ∀ C' : Circuit, C'.n = n → (∀ x, C'.eval x = f x) → C.size ≤ C'.size

theorem nondeg {n : ℕ} {f : (ℕ → Bool) → Bool} {C : Circuit} (hC : IsMin n f C) (k : ℕ)
    (hk : k < C.rgates.length) : ¬ Degenerate C.n (gt C.rgates k) (earl C.rgates k) := by
  rintro ⟨L, hL⟩
  obtain ⟨C', hn, hs, he⟩ := bypass C _ _ _ L (split C.rgates k hk) hL
  have := hC.2.2 C' (hn.trans hC.1) (fun x => (he x).trans (hC.2.1 x))
  omega

/-- A non-degenerate gate reads two distinct earlier wires. -/
theorem shape (n : ℕ) (g : Gate) (e : List Gate) (hnd : ¬ Degenerate n g e) :
    ∃ wa na wb nb, g = ⟨.wire wa na, .wire wb nb⟩ ∧ wa < n + e.length ∧ wb < n + e.length ∧ wa ≠ wb := by
  obtain ⟨a, b⟩ := g
  cases a with
  | const c =>
      exact absurd ⟨if c then b else .const false, fun x => by cases c <;> simp [Gate.eval, Ref.eval]⟩ hnd
  | wire wa na =>
  cases b with
  | const c =>
      exact absurd ⟨if c then .wire wa na else .const false, fun x => by
        cases c <;> simp [Gate.eval, Ref.eval]⟩ hnd
  | wire wb nb =>
  by_cases ha : wa < n + e.length
  swap
  · exact absurd ⟨if na then .wire wb nb else .const false, fun x => by
      simp only [Gate.eval, Ref.eval, val_ge n x e wa (by omega)]
      cases na <;> simp⟩ hnd
  by_cases hb : wb < n + e.length
  swap
  · exact absurd ⟨if nb then .wire wa na else .const false, fun x => by
      simp only [Gate.eval, Ref.eval, val_ge n x e wb (by omega)]
      cases nb <;> simp⟩ hnd
  by_cases hab : wa = wb
  · subst hab
    exact absurd ⟨if na = nb then .wire wa na else .const false, fun x => by
      cases na <;> cases nb <;> cases val n x e wa <;> simp [Gate.eval, Ref.eval]⟩ hnd
  exact ⟨wa, na, wb, nb, rfl, ha, hb, hab⟩

theorem wf_of_min {n : ℕ} {f : (ℕ → Bool) → Bool} {C : Circuit} (hC : IsMin n f C) :
    WF C.n C.rgates := by
  intro k hk u hu
  obtain ⟨wa, na, wb, nb, hg, ha, hb, -⟩ := shape _ _ _ (nondeg hC k hk)
  rw [earl_length _ _ hk.le] at ha hb
  rw [Rd, hg] at hu
  rcases hu with h | h <;> simp only [Ref.Reads] at h <;> omega

/-- Every gate of a minimal circuit is read by a later gate or by the output. -/
theorem alive {n : ℕ} {f : (ℕ → Bool) → Bool} {C : Circuit} (hC : IsMin n f C) (k : ℕ)
    (hk : k < C.rgates.length) :
    (∃ k', k < k' ∧ k' < C.rgates.length ∧ Rd (gt C.rgates k') (C.n + k)) ∨ C.out.Reads (C.n + k) := by
  by_contra hcon
  simp only [not_or, not_exists, not_and] at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hl := earl_length C.rgates k hk.le
  obtain ⟨C', hn, hs, he⟩ := delete_dead C (late C.rgates k) (earl C.rgates k) (gt C.rgates k)
    (split C.rgates k hk) (fun g hg => by
      obtain ⟨k', hk1, hk2, rfl⟩ := mem_late C.rgates k g hg
      rw [hl]
      have := h1 k' hk1 hk2
      simp only [Rd, not_or] at this
      exact this) (by rw [hl]; exact h2)
  have := hC.2.2 C' (hn.trans hC.1) (fun x => (he x).trans (hC.2.1 x))
  omega

/-- Restricting an input deletes at least `K` gates when `K` is at most the cascade count. -/
theorem restrict_le {f : (ℕ → Bool) → Bool} (C : Circuit) (hf : ∀ x, C.eval x = f x) (z : ℕ) (b : Bool)
    (hz : z < C.n) (K : ℕ) (hK : K ≤ cascade C.n z b C.rgates) :
    ∃ s', s' + K ≤ C.size ∧ Realizes C.n (fun x => f (upd x z b)) s' := by
  obtain ⟨C', hn, hs, he, -⟩ := cascade_restriction C z b hz
  exact ⟨C'.size, by omega, C', hn, le_rfl, fun x => by rw [he, hf]⟩

/-! ## Lexicographically minimal circuits -/

/-- Minimal size and, among minimal circuits, fewest readers of wire `n` (the first gate). -/
def LexMin (n : ℕ) (f : (ℕ → Bool) → Bool) (C : Circuit) : Prop :=
  IsMin n f C ∧ ∀ C', IsMin n f C' → readers n C.rgates ≤ readers n C'.rgates

theorem exists_lexmin {n s : ℕ} {f : (ℕ → Bool) → Bool} (h : Realizes n f s) :
    ∃ C, LexMin n f C ∧ C.size ≤ s := by
  classical
  have hex : ∃ m, Realizes n f m := ⟨s, h⟩
  obtain ⟨C0, hn0, hs0, hf0⟩ := Nat.find_spec hex
  have hmin0 : IsMin n f C0 :=
    ⟨hn0, hf0, fun C' hn hf => le_trans hs0 (Nat.find_min' hex ⟨C', hn, le_rfl, hf⟩)⟩
  have hex2 : ∃ r, ∃ C, IsMin n f C ∧ readers n C.rgates = r := ⟨_, C0, hmin0, rfl⟩
  obtain ⟨C, hC, hr⟩ := Nat.find_spec hex2
  refine ⟨C, ⟨hC, fun C' hC' => by rw [hr]; exact Nat.find_min' hex2 ⟨C', hC', rfl⟩⟩, ?_⟩
  have h1 := hC.2.2 C0 hn0 hf0
  have h2 := Nat.find_min' hex h
  omega

theorem val_replace (n : ℕ) (x : ℕ → Bool) (e : List Gate) (g g' : Gate)
    (hg : g'.eval (val n x e) = g.eval (val n x e)) :
    ∀ (later : List Gate) (w : ℕ), val n x (later ++ g' :: e) w = val n x (later ++ g :: e) w
  | [], w => by simp only [List.nil_append, val]; split_ifs <;> simp [hg]
  | h :: later, w => by
      have ih : val n x (later ++ g' :: e) = val n x (later ++ g :: e) :=
        funext (val_replace n x e g g' hg later)
      simp only [List.cons_append, val, List.length_append, List.length_cons]
      rw [ih]

theorem readers_replace (z : ℕ) (later e : List Gate) (g g' : Gate) (hg : Rd g z) (hg' : ¬ Rd g' z) :
    readers z (later ++ g' :: e) + 1 = readers z (later ++ g :: e) := by
  simp only [Rd, not_or] at hg hg'
  obtain ⟨h2a, h2b⟩ := hg'
  rcases hg with h1 | h1 <;>
    simp [readers, List.filter_append, List.filter_cons, h1, h2a, h2b] <;> omega

/-- The value of a reader of `g1 = x_v^av ∧ x_u^au` that also reads `x_v`. -/
theorem rdc (Vn Vv Vu av au p q : Bool) (hV : Vn = ((Vv ^^ av) && (Vu ^^ au))) :
    ((Vn ^^ p) && (Vv ^^ q)) = if (p && (q == av)) then ((Vv ^^ av) && (Vu ^^ !au))
      else if p then (Vv ^^ q) else if q == av then (Vn ^^ false) else false := by
  subst hV
  cases Vv <;> cases Vu <;> cases av <;> cases au <;> cases p <;> cases q <;> rfl

/-- **No reader of the first gate reads its inputs.** Such a reader is degenerate or can read the inputs
directly, which leaves the first gate with fewer readers. -/
theorem noP {n : ℕ} {f : (ℕ → Bool) → Bool} {C : Circuit} (hC : LexMin n f C)
    (hl : 0 < C.rgates.length) (i j : ℕ) (ai aj : Bool)
    (h0 : gt C.rgates 0 = ⟨.wire i ai, .wire j aj⟩) (hi : i < C.n) (hj : j < C.n)
    (k : ℕ) (hk0 : 0 < k) (hk : k < C.rgates.length) (hrd : Rd (gt C.rgates k) C.n) :
    ¬ Rd (gt C.rgates k) i ∧ ¬ Rd (gt C.rgates k) j := by
  have hmin := hC.1
  have hin : ∀ x v, v < C.n → val C.n x (earl C.rgates k) v = x v := fun x v hv => by
    rw [val_earl _ _ _ k hk _ (by omega)]; exact val_input _ _ _ _ hv
  have hV : ∀ x, val C.n x (earl C.rgates k) C.n = ((x i ^^ ai) && (x j ^^ aj)) := by
    intro x
    rw [val_earl _ _ _ k hk _ (by omega)]
    have := val_gate C.n x C.rgates 0 hl
    rw [Nat.add_zero] at this
    rw [this, h0]
    simp [earl, Gate.eval, Ref.eval, val, hi, hj]
  have key : ∀ v u av au, v < C.n → u < C.n →
      (∀ x, val C.n x (earl C.rgates k) C.n = ((x v ^^ av) && (x u ^^ au))) → ¬ Rd (gt C.rgates k) v := by
    intro v u av au hv hu hVv hrv
    obtain ⟨wa, na, wb, nb, hg, -, -, hab⟩ := shape _ _ _ (nondeg hmin k hk)
    have hrd' := hrd
    simp only [Rd, hg, Ref.Reads] at hrd' hrv
    obtain ⟨p, q, hev⟩ : ∃ p q, ∀ V : ℕ → Bool,
        (gt C.rgates k).eval V = ((V C.n ^^ p) && (V v ^^ q)) := by
      rcases hrd' with h1 | h1 <;> rcases hrv with h2 | h2
      · omega
      · subst h1 h2; exact ⟨na, nb, fun V => by simp [hg, Gate.eval, Ref.eval]⟩
      · subst h1 h2; exact ⟨nb, na, fun V => by simp [hg, Gate.eval, Ref.eval, Bool.and_comm]⟩
      · omega
    by_cases hgood : (p && (q == av)) = true
    · let g' : Gate := ⟨.wire v av, .wire u (!au)⟩
      have hg' : ∀ x, g'.eval (val C.n x (earl C.rgates k)) =
          (gt C.rgates k).eval (val C.n x (earl C.rgates k)) := by
        intro x
        rw [hev, hin x v hv, rdc (val C.n x (earl C.rgates k) C.n) (x v) (x u) av au p q (hVv x),
          if_pos hgood]
        simp [g', Gate.eval, Ref.eval, hin x v hv, hin x u hu]
      have hspl := split C.rgates k hk
      let C' : Circuit := ⟨C.n, late C.rgates k ++ g' :: earl C.rgates k, C.out⟩
      have heq : ∀ x, C'.eval x = C.eval x := fun x => by
        have hr : val C.n x (late C.rgates k ++ g' :: earl C.rgates k) =
            val C.n x (late C.rgates k ++ gt C.rgates k :: earl C.rgates k) :=
          funext (val_replace C.n x _ _ _ (hg' x) (late C.rgates k))
        simp only [Circuit.eval, C']
        rw [hr, ← hspl]
      have hsz : C'.size = C.size := by
        simp only [Circuit.size, C']
        conv_rhs => rw [hspl]
        simp
      have hmin' : IsMin n f C' :=
        ⟨hmin.1, fun x => (heq x).trans (hmin.2.1 x), fun C'' hn hf => by
          rw [hsz]; exact hmin.2.2 C'' hn hf⟩
      have hlt := readers_replace C.n (late C.rgates k) (earl C.rgates k) (gt C.rgates k) g' hrd
        (by simp only [Rd, g', Ref.Reads]; omega)
      rw [← hspl] at hlt
      have := hC.2 C' hmin'
      rw [← hmin.1] at this
      simp only [C'] at this
      omega
    · apply nondeg hmin k hk
      refine ⟨if p then .wire v q else if q == av then .wire C.n false else .const false, fun x => ?_⟩
      rw [hev, hin x v hv, rdc (val C.n x (earl C.rgates k) C.n) (x v) (x u) av au p q (hVv x),
        if_neg hgood]
      split_ifs <;> simp [Ref.eval, hin x v hv]
  exact ⟨key i j ai aj hi hj hV, key j i aj ai hj hi (fun x => by rw [hV x, Bool.and_comm])⟩

/-! ## Factoring through the first gate -/

/-- If no other gate and not the output reads `x_i` or `x_j`, then `f` sees them only through the first
gate. -/
theorem factor {n : ℕ} {f : (ℕ → Bool) → Bool} {C : Circuit} (hC : IsMin n f C)
    (hl : 0 < C.rgates.length) (i j : ℕ) (ai aj : Bool)
    (h0 : gt C.rgates 0 = ⟨.wire i ai, .wire j aj⟩) (hi : i < C.n) (hj : j < C.n)
    (hri : ∀ k, 0 < k → k < C.rgates.length → ¬ Rd (gt C.rgates k) i)
    (hrj : ∀ k, 0 < k → k < C.rgates.length → ¬ Rd (gt C.rgates k) j)
    (hoi : ¬ C.out.Reads i) (hoj : ¬ C.out.Reads j) (x y : ℕ → Bool)
    (hxy : ∀ w, w ≠ i → w ≠ j → x w = y w)
    (hg : ((x i ^^ ai) && (x j ^^ aj)) = ((y i ^^ ai) && (y j ^^ aj))) : f x = f y := by
  have hW := wf_of_min hC
  have key : ∀ w, w ≠ i → w ≠ j → val C.n x C.rgates w = val C.n y C.rgates w := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
    intro hwi hwj
    by_cases hw : w < C.n
    · rw [val_input _ _ _ _ hw, val_input _ _ _ _ hw]; exact hxy w hwi hwj
    by_cases hw2 : w < C.n + C.rgates.length
    swap
    · rw [val_ge _ _ _ _ (by omega), val_ge _ _ _ _ (by omega)]
    obtain ⟨k, rfl⟩ : ∃ k, w = C.n + k := ⟨w - C.n, by omega⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [val_gate _ _ _ 0 hl, val_gate _ _ _ 0 hl, h0]
      simpa [earl, Gate.eval, Ref.eval, val, hi, hj] using hg
    · have hk : k < C.rgates.length := by omega
      have hop : ∀ r : Ref, (∀ u, r.Reads u → Rd (gt C.rgates k) u) →
          r.eval (val C.n x C.rgates) = r.eval (val C.n y C.rgates) := by
        intro r hr
        cases r with
        | const c => rfl
        | wire u neg =>
            have hu := hr u (by simp [Ref.Reads])
            have hlt := hW k hk u hu
            have hui : u ≠ i := fun h => hri k hk0 hk (h ▸ hu)
            have huj : u ≠ j := fun h => hrj k hk0 hk (h ▸ hu)
            simp [Ref.eval, ih u hlt hui huj]
      rw [val_gate_wf _ _ _ hW k hk, val_gate_wf _ _ _ hW k hk]
      unfold Gate.eval
      rw [hop (gt C.rgates k).a (fun u hu => Or.inl hu), hop (gt C.rgates k).b (fun u hu => Or.inr hu)]
  rw [← hC.2.1 x, ← hC.2.1 y]
  unfold Circuit.eval
  cases ho : C.out with
  | const c => rfl
  | wire u neg =>
      rw [ho] at hoi hoj
      simp only [Ref.Reads] at hoi hoj
      simp [Ref.eval, key u hoi hoj]

/-! ## The facts each first-gate input contributes -/

/-- `g` has a circuit with at least `k` gates fewer than `s`. -/
def RLe (n : ℕ) (g : (ℕ → Bool) → Bool) (s k : ℕ) : Prop := ∃ s', s' + k ≤ s ∧ Realizes n g s'

/-- `g` is constant. -/
def Cst (g : (ℕ → Bool) → Bool) : Prop := ∀ x y, g x = g y

/-- What fixing a first-gate input `v` (controlling value `bv`, `r` gate readers) deletes from a circuit
with `s` gates. -/
def Facts (n : ℕ) (f : (ℕ → Bool) → Bool) (s v : ℕ) (bv : Bool) (r : ℕ) : Prop :=
  1 ≤ r ∧ (∀ b, RLe n (fun x => f (upd x v b)) s r) ∧ RLe n (fun x => f (upd x v bv)) s (r + 1) ∧
  (r = 2 → ∃ c : Bool,
    (c ≠ bv → RLe n (fun x => f (upd x v c)) s 3 ∨
      (Cst (fun x => f (upd x v c)) ∧ RLe n (fun x => f (upd x v c)) s 2)) ∧
    (c = bv → RLe n (fun x => f (upd x v bv)) s 4 ∨
      (Cst (fun x => f (upd x v bv)) ∧ RLe n (fun x => f (upd x v bv)) s 3)))

theorem card3 {a b c : ℕ} (h1 : a ≠ b) (h2 : a ≠ c) (h3 : b ≠ c) : ({a, b, c} : Finset ℕ).card = 3 := by
  rw [Finset.card_insert_of_notMem (by simp [h1, h2]), Finset.card_pair h3]

theorem card4 {a b c d : ℕ} (h1 : a ≠ b) (h2 : a ≠ c) (h3 : a ≠ d) (h4 : b ≠ c) (h5 : b ≠ d)
    (h6 : c ≠ d) : ({a, b, c, d} : Finset ℕ).card = 4 := by
  rw [Finset.card_insert_of_notMem (by simp [h1, h2, h3]), card3 h4 h5 h6]

section facts
open Classical

variable {n : ℕ} {f : (ℕ → Bool) → Bool} {C : Circuit}

theorem kill (hC : IsMin n f C) (z : ℕ) (b : Bool) (hz : z < C.n) (K : Finset ℕ)
    (hK : ∀ k ∈ K, k < C.rgates.length ∧ ∃ u, Rd (gt C.rgates k) u ∧ ConstUnder C.n z b C.rgates u) :
    RLe n (fun x => f (upd x z b)) C.size K.card := by
  obtain ⟨s', hs, hr⟩ := restrict_le C hC.2.1 z b hz K.card (cascade_ge _ _ _ _ (wf_of_min hC) K hK)
  exact ⟨s', hs, hC.1 ▸ hr⟩

theorem cst_out (hC : IsMin n f C) (z : ℕ) (b : Bool) (w : ℕ) (ho : C.out.Reads w)
    (hw : ConstUnder C.n z b C.rgates w) : Cst (fun x => f (upd x z b)) := by
  obtain ⟨c, hc⟩ := hw
  intro x y
  simp only [← hC.2.1, Circuit.eval]
  cases hO : C.out with
  | const d => rfl
  | wire u neg => rw [hO] at ho; simp only [Ref.Reads] at ho; subst ho; simp [Ref.eval, hc]

theorem out_reads (hC : IsMin n f C) (hl : 0 < C.rgates.length) (w : ℕ) (h : C.out.Reads w) :
    w = C.n + (C.rgates.length - 1) := by
  have hlast : C.out.Reads (C.n + (C.rgates.length - 1)) := by
    rcases alive hC (C.rgates.length - 1) (by omega) with ⟨k', h1, h2, -⟩ | h
    · omega
    · exact h
  cases hO : C.out with
  | const d => rw [hO] at h; exact h.elim
  | wire u neg => rw [hO] at h hlast; simp only [Ref.Reads] at h hlast; omega

theorem two_reads (hC : IsMin n f C) (k : ℕ) (hk : k < C.rgates.length) (u1 u2 : ℕ) (h12 : u1 ≠ u2)
    (h1 : Rd (gt C.rgates k) u1) (h2 : Rd (gt C.rgates k) u2) :
    ∀ u, Rd (gt C.rgates k) u → u = u1 ∨ u = u2 := by
  obtain ⟨wa, na, wb, nb, hg, -⟩ := shape _ _ _ (nondeg hC k hk)
  intro u hu
  simp only [Rd, hg, Ref.Reads] at h1 h2 hu
  omega

theorem facts_v (hC : LexMin n f C) (hl : 2 ≤ C.rgates.length) (v : ℕ) (av : Bool) (hv : v < C.n)
    (h0 : (gt C.rgates 0).a = .wire v av ∨ (gt C.rgates 0).b = .wire v av)
    (hnp : ∀ k, 0 < k → k < C.rgates.length → Rd (gt C.rgates k) C.n → ¬ Rd (gt C.rgates k) v) :
    Facts n f C.size v av (readers v C.rgates) := by
  have hmin := hC.1
  have hW := wf_of_min hmin
  have hlen0 : 0 < C.rgates.length := by omega
  obtain ⟨k1, hk10, hk1, hk1r⟩ : ∃ k1, 0 < k1 ∧ k1 < C.rgates.length ∧ Rd (gt C.rgates k1) C.n := by
    rcases alive hmin 0 hlen0 with ⟨k', h1, h2, h3⟩ | h
    · exact ⟨k', h1, h2, by simpa using h3⟩
    · have := out_reads hmin hlen0 _ h; omega
  have hcv : ∀ b, ConstUnder C.n v b C.rgates v := fun b => cu_input _ _ _ _ hv
  have hc0 : ConstUnder C.n v av C.rgates C.n := by
    have := cu_ctrl C.n v av C.rgates hW 0 hlen0 v av h0
      (fun x => by rw [val_input _ _ _ _ hv, upd_same])
    simpa using this
  set S := (Finset.range C.rgates.length).filter fun k => Rd (gt C.rgates k) v with hS
  have hSr : readers v C.rgates = S.card := readers_eq v C.rgates
  have hmemS : ∀ k, k ∈ S ↔ k < C.rgates.length ∧ Rd (gt C.rgates k) v := fun k => by simp [hS]
  have h0S : 0 ∈ S :=
    (hmemS 0).2 ⟨hlen0, by simp only [Rd]; rcases h0 with h | h <;> simp [h, Ref.Reads]⟩
  have hk1S : k1 ∉ S := fun h => hnp k1 hk10 hk1 hk1r ((hmemS k1).1 h).2
  have killS : ∀ b, ∀ k ∈ S,
      k < C.rgates.length ∧ ∃ u, Rd (gt C.rgates k) u ∧ ConstUnder C.n v b C.rgates u :=
    fun b k hk => ⟨((hmemS k).1 hk).1, v, ((hmemS k).1 hk).2, hcv b⟩
  have hk1kill : k1 < C.rgates.length ∧ ∃ u, Rd (gt C.rgates k1) u ∧ ConstUnder C.n v av C.rgates u :=
    ⟨hk1, C.n, hk1r, hc0⟩
  refine ⟨?_, fun b => ?_, ?_, fun h2 => ?_⟩
  · rw [hSr]; exact Finset.card_pos.2 ⟨0, h0S⟩
  · rw [hSr]; exact kill hmin v b hv S (killS b)
  · have := kill hmin v av hv (insert k1 S) (fun k hk => by
      rcases Finset.mem_insert.1 hk with rfl | hk
      · exact hk1kill
      · exact killS av k hk)
    rwa [Finset.card_insert_of_notMem hk1S, ← hSr] at this
  · rw [hSr] at h2
    obtain ⟨k2, hk2⟩ : ∃ k2, S.erase 0 = {k2} :=
      Finset.card_eq_one.1 (by rw [Finset.card_erase_of_mem h0S]; omega)
    have hk2e : k2 ∈ S.erase 0 := by rw [hk2]; exact Finset.mem_singleton_self k2
    have hk2S : k2 ∈ S := Finset.mem_of_mem_erase hk2e
    have hk20 : k2 ≠ 0 := Finset.ne_of_mem_erase hk2e
    obtain ⟨hk2l, hk2v⟩ := (hmemS k2).1 hk2S
    obtain ⟨c, hc⟩ : ∃ c, (gt C.rgates k2).a = .wire v c ∨ (gt C.rgates k2).b = .wire v c := by
      obtain ⟨wa, na, wb, nb, hg, -⟩ := shape _ _ _ (nondeg hmin k2 hk2l)
      simp only [Rd, hg, Ref.Reads] at hk2v
      rcases hk2v with h | h
      · exact ⟨na, Or.inl (by rw [hg, h])⟩
      · exact ⟨nb, Or.inr (by rw [hg, h])⟩
    have hck2 : ConstUnder C.n v c C.rgates (C.n + k2) :=
      cu_ctrl C.n v c C.rgates hW k2 hk2l v c hc (fun x => by rw [val_input _ _ _ _ hv, upd_same])
    have kill0 : ∀ b, 0 < C.rgates.length ∧ ∃ u, Rd (gt C.rgates 0) u ∧ ConstUnder C.n v b C.rgates u :=
      fun b => killS b 0 h0S
    have killk2 : ∀ b,
        k2 < C.rgates.length ∧ ∃ u, Rd (gt C.rgates k2) u ∧ ConstUnder C.n v b C.rgates u :=
      fun b => killS b k2 hk2S
    refine ⟨c, fun hne => ?_, fun heq => ?_⟩
    · rcases alive hmin k2 hk2l with ⟨k3, h31, h32, h33⟩ | hout2
      · left
        have := kill hmin v c hv {0, k2, k3} (fun k hk => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hk
          rcases hk with rfl | rfl | rfl
          · exact kill0 c
          · exact killk2 c
          · exact ⟨h32, _, h33, hck2⟩)
        rwa [card3 (by omega) (by omega) (by omega)] at this
      · right
        refine ⟨cst_out hmin v c _ hout2 hck2, ?_⟩
        have := kill hmin v c hv {0, k2} (fun k hk => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hk
          rcases hk with rfl | rfl
          · exact kill0 c
          · exact killk2 c)
        rwa [Finset.card_pair (by omega)] at this
    · rw [heq] at hck2
      have hk1k2 : k1 ≠ k2 := fun h => hk1S (h ▸ hk2S)
      have K3 : RLe n (fun x => f (upd x v av)) C.size 3 := by
        have := kill hmin v av hv {0, k2, k1} (fun k hk => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hk
          rcases hk with rfl | rfl | rfl
          · exact kill0 av
          · exact killk2 av
          · exact hk1kill)
        rwa [card3 (by omega) (by omega) (Ne.symm hk1k2)] at this
      rcases alive hmin k2 hk2l with ⟨k3, h31, h32, h33⟩ | hout2
      · by_cases h3 : k3 = k1
        · have h33' : Rd (gt C.rgates k1) (C.n + k2) := h3 ▸ h33
          have hlt21 := hW k1 hk1 _ h33'
          have hrd2 := two_reads hmin k1 hk1 C.n (C.n + k2) (by omega) hk1r h33'
          have hck1 : ConstUnder C.n v av C.rgates (C.n + k1) := cu_gate C.n v av C.rgates hW k1 hk1
            (fun u neg h => by
              rcases hrd2 u (Or.inl (by simp [h, Ref.Reads])) with rfl | rfl
              · exact hc0
              · exact hck2)
            (fun u neg h => by
              rcases hrd2 u (Or.inr (by simp [h, Ref.Reads])) with rfl | rfl
              · exact hc0
              · exact hck2)
          rcases alive hmin k1 hk1 with ⟨k4, h41, h42, h43⟩ | hout3
          · left
            have := kill hmin v av hv {0, k2, k1, k4} (fun k hk => by
              simp only [Finset.mem_insert, Finset.mem_singleton] at hk
              rcases hk with rfl | rfl | rfl | rfl
              · exact kill0 av
              · exact killk2 av
              · exact hk1kill
              · exact ⟨h42, _, h43, hck1⟩)
            rwa [card4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)] at this
          · right; exact ⟨cst_out hmin v av _ hout3 hck1, K3⟩
        · left
          have := kill hmin v av hv {0, k2, k1, k3} (fun k hk => by
            simp only [Finset.mem_insert, Finset.mem_singleton] at hk
            rcases hk with rfl | rfl | rfl | rfl
            · exact kill0 av
            · exact killk2 av
            · exact hk1kill
            · exact ⟨h32, _, h33, hck2⟩)
          rwa [card4 (by omega) (by omega) (by omega) (Ne.symm hk1k2) (by omega) (Ne.symm h3)] at this
      · right; exact ⟨cst_out hmin v av _ hout2 hck2, K3⟩

/-- **First-gate facts.** A lexicographically minimal circuit with at least two gates has a first gate
`x_i^ai ∧ x_j^aj` with `i ≠ j`; each input contributes `Facts`, and if both have one reader then `f`
factors through the first gate. -/
theorem first_gate (hC : LexMin n f C) (hl : 2 ≤ C.rgates.length) :
    ∃ i j ai aj, i ≠ j ∧ i < n ∧ j < n ∧ Facts n f C.size i ai (readers i C.rgates) ∧
      Facts n f C.size j aj (readers j C.rgates) ∧
      (readers i C.rgates = 1 → readers j C.rgates = 1 → ∀ x y, (∀ w, w ≠ i → w ≠ j → x w = y w) →
        ((x i ^^ ai) && (x j ^^ aj)) = ((y i ^^ ai) && (y j ^^ aj)) → f x = f y) := by
  have hmin := hC.1
  have hn := hmin.1
  have hlen0 : 0 < C.rgates.length := by omega
  obtain ⟨i, ai, j, aj, hg, hi, hj, hij⟩ := shape _ _ _ (nondeg hmin 0 hlen0)
  simp only [earl_length _ _ hlen0.le, Nat.add_zero] at hi hj
  have hnp := noP hC hlen0 i j ai aj hg hi hj
  refine ⟨i, j, ai, aj, hij, by omega, by omega,
    facts_v hC hl i ai hi (Or.inl (by rw [hg])) (fun k h1 h2 h3 => (hnp k h1 h2 h3).1),
    facts_v hC hl j aj hj (Or.inr (by rw [hg])) (fun k h1 h2 h3 => (hnp k h1 h2 h3).2),
    fun hri hrj => ?_⟩
  have only : ∀ v, readers v C.rgates = 1 → Rd (gt C.rgates 0) v →
      ∀ k, 0 < k → k < C.rgates.length → ¬ Rd (gt C.rgates k) v := by
    intro v hr h0 k hk0 hk hkv
    have := card_le_readers v C.rgates {0, k} (fun k' hk' => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk'
      rcases hk' with rfl | rfl
      · exact ⟨hlen0, h0⟩
      · exact ⟨hk, hkv⟩)
    rw [Finset.card_pair (by omega)] at this
    omega
  exact factor hmin hlen0 i j ai aj hg hi hj (only i hri (by simp [Rd, hg, Ref.Reads]))
    (only j hrj (by simp [Rd, hg, Ref.Reads]))
    (fun h => by have := out_reads hmin hlen0 i h; omega) (fun h => by have := out_reads hmin hlen0 j h; omega)

/-- A minimal circuit with at most one gate computes a constant, a literal, or one gate. -/
theorem small (hC : IsMin n f C) (hl : C.rgates.length ≤ 1) :
    (∃ c, ∀ x, f x = c) ∨ (∃ u < n, ∃ neg, ∀ x, f x = (x u ^^ neg)) ∨
      (C.rgates.length = 1 ∧ ∃ i j ai aj neg, i ≠ j ∧ i < n ∧ j < n ∧
        ∀ x, f x = (((x i ^^ ai) && (x j ^^ aj)) ^^ neg)) := by
  have hn := hC.1
  have hev : ∀ x, f x = C.out.eval (val C.n x C.rgates) := fun x => (hC.2.1 x).symm
  -- an output reading wire `w` with `w ≠ C.n` sees a constant or a literal
  have lit : ∀ w neg, C.out = .wire w neg → w ≠ C.n → ¬ (C.rgates.length = 1 ∧ w = C.n) →
      (∃ c, ∀ x, f x = c) ∨ (∃ u < n, ∃ neg, ∀ x, f x = (x u ^^ neg)) := by
    intro w neg hO hw _
    by_cases hwn : w < C.n
    · exact Or.inr ⟨w, by omega, neg, fun x => by rw [hev, hO]; simp [Ref.eval, val_input _ _ _ _ hwn]⟩
    · left
      refine ⟨neg, fun x => ?_⟩
      rw [hev, hO]
      have : C.n + C.rgates.length ≤ w := by
        rcases Nat.lt_or_ge C.rgates.length 1 with h | h
        · omega
        · have := alive hC 0 (by omega)
          rcases this with ⟨k', h1, h2, -⟩ | h3
          · omega
          · rw [hO] at h3; simp only [Ref.Reads] at h3; omega
      simp [Ref.eval, val_ge _ _ _ _ this]
  cases hO : C.out with
  | const c => exact Or.inl ⟨c, fun x => by rw [hev, hO]; rfl⟩
  | wire w neg =>
      by_cases hw : w = C.n ∧ C.rgates.length = 1
      · right; right
        obtain ⟨hw, h1⟩ := hw
        refine ⟨h1, ?_⟩
        obtain ⟨i, ai, j, aj, hg, hi, hj, hij⟩ := shape _ _ _ (nondeg hC 0 (by omega))
        simp only [earl_length _ _ (by omega : 0 ≤ C.rgates.length), Nat.add_zero] at hi hj
        refine ⟨i, j, ai, aj, neg, hij, by omega, by omega, fun x => ?_⟩
        rw [hev, hO, hw]
        have := val_gate C.n x C.rgates 0 (by omega)
        rw [Nat.add_zero] at this
        simp only [Ref.eval, this, hg]
        simp [earl, Gate.eval, Ref.eval, val, hi, hj]
      · by_cases hwc : w = C.n
        · -- the only gate is never read when there are no gates
          have h0 : C.rgates.length = 0 := by omega
          left
          refine ⟨neg, fun x => ?_⟩
          rw [hev, hO]
          simp [Ref.eval, val_ge _ _ _ _ (by omega : C.n + C.rgates.length ≤ w)]
        · exact (lit w neg hO hwc (by omega)).elim Or.inl (fun h => Or.inr (Or.inl h))

end facts

end CircuitLemmas.GateElim.FirstGate
