/-
The XNOR conjunction lower bound (2026-11-26).

`xnorConj P x` is the AND of `x a == x b` over a list `P` of disjoint pairs of inputs. In the free-NOT
binary AIG model of `GateElim`, every circuit for it has at least `4 |P| - 1` gates:
`xnorConj_lower`, and `xnorConj_std_lower` for the pairs `(2j, 2j+1)`, `j < q`, which is the function
`F_q` that the six-bit SAT fragment `11x10y` plus `110100` restricts `SAT_n` to.

Proof (gate elimination, strong induction on the circuit size, then on `|P|`):
* a degenerate first gate, a first gate on an input outside the pairs, or a dead first gate gives a
  smaller circuit for the same function;
* otherwise the first gate `g0` is `l_u ∧ l_v` on two distinct inputs `u, v` of the pairs;
* each of `u, v` has a second reader: if only `g0` read `v`, then with `x_u` fixed to make `l_u` false
  the circuit would ignore `x_v`, but the function still depends on `x_v`;
* `g0` is not the output (the same argument) and has a reader;
* one of `z ∈ {u, v}` therefore has two distinct later gates reading `z` or `g0` (a single gate cannot
  read the three wires `u`, `v`, `g0`), and fixing `x_z` to make `l_z` false makes `g0` constant, so the
  cascade deletes `g0` and those two gates (`cascade_restriction`): three gates;
* the restriction is `xnorConj P' ∧ (x_z' == c)` for the partner `z'`, and the literal factor costs one
  more gate (`literal_extension_phase`).
No canalizing replacement is needed: when the only reader of `g0` is the second reader of `u`, it does not
read `v`, so fixing `v` instead deletes three gates.
-/
import CircuitLemmas.GateElim

namespace CircuitLemmas.GateElim

/-! ## Literal extension with either phase -/

/-- **Independent literal extension, either phase.** If `g` is nonconstant and ignores input `z`, then
`C(g ∧ (x_z == c)) ≥ C(g) + 1`. -/
theorem literal_extension_phase {n s z : ℕ} (hz : z < n) (c : Bool) (g : (ℕ → Bool) → Bool)
    (hindep : ∀ x d, g (upd x z d) = g x) (h1 : ∃ x, g x = true) (h0 : ∃ x, g x = false)
    (h : Realizes n (fun x => g x && (x z == c)) s) : Realizes n g (s - 1) := by
  obtain ⟨C, hn, hs, hf⟩ := h
  have hzC : z < C.n := hn ▸ hz
  by_cases hread : ∃ gj ∈ C.rgates, gj.a.Reads z ∨ gj.b.Reads z
  · obtain ⟨gj, hmem, hgj⟩ := hread
    obtain ⟨later, earlier, hsplit⟩ := List.append_of_mem hmem
    set C1 := C.restrict z c
    have hC1 : C1.rgates = later.map (Gate.restrict z c) ++
        Gate.restrict z c gj :: earlier.map (Gate.restrict z c) := by
      simp [C1, Circuit.restrict, hsplit]
    obtain ⟨L, hL⟩ := Gate.restrict_literal z c gj hgj
    obtain ⟨C', hn', hsize, heval⟩ := bypass C1 _ _ _ L hC1 (fun x => hL _)
    refine ⟨C', hn'.trans hn, ?_, fun x => ?_⟩
    · have : C1.size = C.size := Circuit.size_restrict C z c
      omega
    · rw [heval, Circuit.eval_restrict C z c hzC, hf]
      simp [hindep]
  · simp only [not_exists, not_and, not_or] at hread
    have hg : ∀ gj ∈ C.rgates, ¬ gj.a.Reads z ∧ ¬ gj.b.Reads z := fun gj hm => hread gj hm
    by_cases ho : C.out.Reads z
    · exfalso
      obtain ⟨x0, hx0⟩ := h0
      cases hout : C.out with
      | const _ => rw [hout] at ho; simp [Ref.Reads] at ho
      | wire w neg =>
          rw [hout] at ho; simp only [Ref.Reads] at ho; subst ho
          have e := hf (upd x0 w (!neg))
          simp only [Circuit.eval, hout, Ref.eval, val_input C.n _ C.rgates w hzC, upd_same,
            hindep, hx0, Bool.false_and] at e
          cases neg <;> simp at e
    · exfalso
      obtain ⟨x1, hx1⟩ := h1
      have e1 := hf (upd x1 z c)
      have e0 := hf (upd x1 z (!c))
      rw [Circuit.eval_upd_of_not_reads C z _ hzC hg ho] at e1 e0
      simp only [hindep, hx1, upd_same, Bool.true_and] at e1 e0
      rw [e1] at e0
      cases c <;> simp at e0

/-! ## The function -/

/-- The AND of `x a == x b` over the pairs `(a, b) ∈ P`. -/
def xnorConj (P : List (ℕ × ℕ)) (x : ℕ → Bool) : Bool := P.all fun p => x p.1 == x p.2

/-- Input `w` occurs in some pair. -/
def Supp (P : List (ℕ × ℕ)) (w : ℕ) : Prop := ∃ p ∈ P, p.1 = w ∨ p.2 = w

/-- The pairs are disjoint and each pair has two distinct inputs. -/
def PairsNodup (P : List (ℕ × ℕ)) : Prop := (P.flatMap fun p => [p.1, p.2]).Nodup

theorem pairsNodup_cons {p : ℕ × ℕ} {P : List (ℕ × ℕ)} (h : PairsNodup (p :: P)) :
    p.1 ≠ p.2 ∧ ¬ Supp P p.1 ∧ ¬ Supp P p.2 ∧ PairsNodup P := by
  unfold PairsNodup at h
  simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
    List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false, not_or, not_exists, not_and] at h
  obtain ⟨⟨hne, h1⟩, h2, h3⟩ := h
  refine ⟨hne, ?_, ?_, h3⟩
  · rintro ⟨q, hq, hq'⟩
    rcases hq' with e | e
    · exact (h1 q hq).1 e.symm
    · exact (h1 q hq).2 e.symm
  · rintro ⟨q, hq, hq'⟩
    rcases hq' with e | e
    · exact (h2 q hq).1 e.symm
    · exact (h2 q hq).2 e.symm

theorem pairsNodup_perm {P Q : List (ℕ × ℕ)} (h : P.Perm Q) (hP : PairsNodup P) : PairsNodup Q :=
  (h.flatMap_right _).nodup_iff.mp hP

theorem xnorConj_perm {P Q : List (ℕ × ℕ)} (h : P.Perm Q) (x : ℕ → Bool) :
    xnorConj P x = xnorConj Q x := by
  unfold xnorConj
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  exact ⟨fun H q hq => H q (h.mem_iff.mpr hq), fun H q hq => H q (h.mem_iff.mp hq)⟩

/-- Facts about a pair `p ∈ P`, read off `p :: P.erase p`. -/
theorem pair_facts {P : List (ℕ × ℕ)} (hnd : PairsNodup P) {p : ℕ × ℕ} (hp : p ∈ P) :
    p.1 ≠ p.2 ∧ ¬ Supp (P.erase p) p.1 ∧ ¬ Supp (P.erase p) p.2 ∧ PairsNodup (P.erase p) :=
  pairsNodup_cons (pairsNodup_perm (List.perm_cons_erase hp) hnd)

theorem xnorConj_upd_of_not_supp (P : List (ℕ × ℕ)) (u : ℕ) (hu : ¬ Supp P u) (x : ℕ → Bool)
    (b : Bool) : xnorConj P (upd x u b) = xnorConj P x := by
  induction P with
  | nil => rfl
  | cons p P ih =>
      have h1 : p.1 ≠ u := fun h => hu ⟨p, List.mem_cons_self, Or.inl h⟩
      have h2 : p.2 ≠ u := fun h => hu ⟨p, List.mem_cons_self, Or.inr h⟩
      have hu' : ¬ Supp P u := fun ⟨q, hq, h⟩ => hu ⟨q, List.mem_cons_of_mem _ hq, h⟩
      simp only [xnorConj, List.all_cons] at ih ⊢
      rw [ih hu']
      simp [upd, h1, h2]

theorem xnorConj_const (P : List (ℕ × ℕ)) (c : Bool) : xnorConj P (fun _ => c) = true := by
  simp [xnorConj]

/-- Flipping one input of a satisfying constant assignment falsifies the pair containing it. -/
theorem xnorConj_flip (P : List (ℕ × ℕ)) (hnd : PairsNodup P) (t : ℕ) (ht : Supp P t) (c : Bool) :
    xnorConj P (upd (fun _ => c) t (!c)) = false := by
  obtain ⟨p, hp, hpt⟩ := ht
  have hne := (pair_facts hnd hp).1
  by_contra hcon
  have htrue : xnorConj P (upd (fun _ => c) t (!c)) = true := by simpa using hcon
  rw [xnorConj, List.all_eq_true] at htrue
  have := htrue p hp
  rcases hpt with h | h
  · subst h; cases c <;> simp [upd, Ne.symm hne] at this
  · subst h; cases c <;> simp [upd, hne] at this

/-- A function that ignores an input of the pairs is not `xnorConj P`. -/
theorem not_ignores (P : List (ℕ × ℕ)) (hnd : PairsNodup P) (t : ℕ) (ht : Supp P t)
    (f : (ℕ → Bool) → Bool) (hf : ∀ x, f x = xnorConj P x) (hign : ∀ x b, f (upd x t b) = f x) :
    False := by
  have e := hign (fun _ => false) true
  rw [hf, hf, xnorConj_const] at e
  have h := xnorConj_flip P hnd t ht false
  simp only [Bool.not_false] at h
  rw [h] at e
  exact absurd e (by decide)

/-- Fixing an input of a pair leaves the other pairs and a literal on its partner. -/
theorem xnorConj_restrict {n : ℕ} (P : List (ℕ × ℕ)) (hnd : PairsNodup P)
    (hlt : ∀ p ∈ P, p.1 < n ∧ p.2 < n) (z : ℕ) (hz : Supp P z) :
    ∃ p ∈ P, ∃ z', z' < n ∧ ¬ Supp (P.erase p) z' ∧
      ∀ x c, xnorConj P (upd x z c) = (xnorConj (P.erase p) x && (x z' == c)) := by
  obtain ⟨p, hp, hpz⟩ := hz
  obtain ⟨hne, hs1, hs2, -⟩ := pair_facts hnd hp
  have hperm := List.perm_cons_erase hp
  rcases hpz with h | h
  · refine ⟨p, hp, p.2, (hlt p hp).2, hs2, fun x c => ?_⟩
    rw [xnorConj_perm hperm]
    simp only [xnorConj, List.all_cons]
    have e := xnorConj_upd_of_not_supp (P.erase p) z (h ▸ hs1) x c
    simp only [xnorConj] at e
    rw [e, ← h]
    rcases Bool.eq_false_or_eq_true (x p.2) with e2 | e2 <;> cases c <;> simp [upd, Ne.symm hne, e2]
  · refine ⟨p, hp, p.1, (hlt p hp).1, hs1, fun x c => ?_⟩
    rw [xnorConj_perm hperm]
    simp only [xnorConj, List.all_cons]
    have e := xnorConj_upd_of_not_supp (P.erase p) z (h ▸ hs2) x c
    simp only [xnorConj] at e
    rw [e, ← h]
    rcases Bool.eq_false_or_eq_true (x p.1) with e2 | e2 <;> cases c <;> simp [upd, hne, e2]

/-! ## Circuit facts -/

/-- The first gate either equals a literal or ANDs two distinct inputs. -/
theorem first_gate_cases (n : ℕ) (g : Gate) :
    Degenerate n g [] ∨ ∃ u nu v nv, g = ⟨.wire u nu, .wire v nv⟩ ∧ u < n ∧ v < n ∧ u ≠ v := by
  obtain ⟨a, b⟩ := g
  cases a with
  | const c =>
      left; obtain ⟨L, hL⟩ := Gate.eval_const_left c b; exact ⟨L, fun x => hL _⟩
  | wire u nu =>
      cases b with
      | const c =>
          left; obtain ⟨L, hL⟩ := Gate.eval_const_right c (.wire u nu); exact ⟨L, fun x => hL _⟩
      | wire v nv =>
          by_cases hu : u < n
          · by_cases hv : v < n
            · by_cases huv : u = v
              · left; subst huv
                refine ⟨if nu = nv then .wire u nu else .const false, fun x => ?_⟩
                cases nu <;> cases nv <;> cases h : val n x [] u <;> simp [Gate.eval, Ref.eval, h]
              · right; exact ⟨u, nu, v, nv, rfl, hu, hv, huv⟩
            · left
              have h0 : ∀ x, val n x [] v = false := fun x => by simp [val, hv]
              refine ⟨if nv then .wire u nu else .const false, fun x => ?_⟩
              cases nv <;> simp [Gate.eval, Ref.eval, h0]
          · left
            have h0 : ∀ x, val n x [] u = false := fun x => by simp [val, hu]
            refine ⟨if nu then .wire v nv else .const false, fun x => ?_⟩
            cases nu <;> simp [Gate.eval, Ref.eval, h0]

theorem one_le_readers {z : ℕ} {rgs : List Gate} {g : Gate} (hg : g ∈ rgs)
    (h : g.a.Reads z ∨ g.b.Reads z) : 1 ≤ readers z rgs := by
  unfold readers
  exact List.length_pos_of_mem (List.mem_filter.mpr ⟨hg, by simp only [decide_eq_true_eq]; exact h⟩)

/-- If no later gate reads `v`, flipping `v` changes no other wire as long as the first gate keeps its
value. -/
theorem val_flip_first (n : ℕ) (g0 : Gate) (v : ℕ) (x : ℕ → Bool) (b : Bool)
    (h0 : g0.eval (val n (upd x v b) []) = g0.eval (val n x [])) :
    ∀ later : List Gate, (∀ g ∈ later, ¬ g.a.Reads v ∧ ¬ g.b.Reads v) →
      ∀ w, w ≠ v → val n (upd x v b) (later ++ [g0]) w = val n x (later ++ [g0]) w
  | [], _, w, hw => by
      simp only [List.nil_append, val, List.length_nil, Nat.add_zero]
      split_ifs
      · exact h0
      · simp [upd, hw]
      · rfl
  | g :: later, hr, w, hw => by
      have ih := val_flip_first n g0 v x b h0 later (fun g hg => hr g (List.mem_cons_of_mem _ hg))
      obtain ⟨ha, hb⟩ := hr g List.mem_cons_self
      simp only [List.cons_append, val]
      split_ifs
      · simp only [Gate.eval]
        rw [Ref.eval_congr _ _ _ g.a ha ih, Ref.eval_congr _ _ _ g.b hb ih]
      · exact ih w hw

theorem eval_flip_first (C : Circuit) (later : List Gate) (g0 : Gate) (hC : C.rgates = later ++ [g0])
    (v : ℕ) (hno : ∀ g ∈ later, ¬ g.a.Reads v ∧ ¬ g.b.Reads v) (ho : ¬ C.out.Reads v)
    (x : ℕ → Bool) (b : Bool) (h0 : g0.eval (val C.n (upd x v b) []) = g0.eval (val C.n x [])) :
    C.eval (upd x v b) = C.eval x := by
  simp only [Circuit.eval, hC]
  exact Ref.eval_congr _ _ _ C.out ho (val_flip_first C.n g0 v x b h0 later hno)

/-- **Second reader.** In a circuit for `xnorConj P` whose first gate is `l_u ∧ l_v`, some later gate
reads `v`. -/
theorem second_reader {n : ℕ} {P : List (ℕ × ℕ)} (hnd : PairsNodup P) (C : Circuit) (hn : C.n = n)
    (hf : ∀ x, C.eval x = xnorConj P x) (later : List Gate) (g0 : Gate)
    (hC : C.rgates = later ++ [g0]) {u v : ℕ} {nu nv : Bool} (hu : u < n) (hv : v < n) (huv : u ≠ v)
    (hsu : Supp P u) (hsv : Supp P v)
    (hg0 : ∀ y, g0.eval y = (Bool.xor (y u) nu && Bool.xor (y v) nv)) :
    ∃ g ∈ later, g.a.Reads v ∨ g.b.Reads v := by
  by_contra hno
  simp only [not_exists, not_and, not_or] at hno
  by_cases ho : C.out.Reads v
  · -- the output is the literal `x_v`, which ignores `x_u`
    apply not_ignores P hnd u hsu C.eval hf
    intro x b
    have hvC : v < C.n := hn ▸ hv
    cases hout : C.out with
    | const _ => rw [hout] at ho; simp [Ref.Reads] at ho
    | wire w neg =>
        rw [hout] at ho; simp only [Ref.Reads] at ho; subst ho
        simp only [Circuit.eval, hout, Ref.eval, val_input C.n _ C.rgates w hvC, upd,
          if_neg (Ne.symm huv)]
  · -- only `g0` reads `v`; with `l_u` false the circuit ignores `x_v`
    have hx := eval_flip_first C later g0 hC v hno ho (fun _ => nu) (!nu) (by
      rw [hg0, hg0, val_input C.n _ [] u (hn ▸ hu), val_input C.n _ [] u (hn ▸ hu)]
      simp [upd, huv])
    rw [hf, hf, xnorConj_const, xnorConj_flip P hnd v hsv nu] at hx
    exact absurd hx (by decide)

/-! ## Counting gates -/

open Classical in
/-- The number of gates of a list satisfying `p`. -/
noncomputable def cnt (p : Gate → Prop) : List Gate → ℕ
  | [] => 0
  | g :: l => (if p g then 1 else 0) + cnt p l

theorem cnt_pos {p : Gate → Prop} : ∀ {l : List Gate} {a : Gate}, a ∈ l → p a → 1 ≤ cnt p l
  | [], _, ha, _ => by simp at ha
  | g :: l, a, ha, hpa => by
      simp only [cnt]
      rcases List.mem_cons.mp ha with rfl | ha'
      · rw [if_pos hpa]; omega
      · have := cnt_pos ha' hpa; omega

theorem cnt_le_one {p : Gate → Prop} : ∀ {l : List Gate} {a b : Gate}, cnt p l ≤ 1 → a ∈ l → b ∈ l →
    p a → p b → a = b
  | [], _, _, _, ha, _, _, _ => by simp at ha
  | g :: l, a, b, h, ha, hb, hpa, hpb => by
      simp only [cnt] at h
      rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
      · rfl
      · have := cnt_pos hb' hpb; rw [if_pos hpa] at h; omega
      · have := cnt_pos ha' hpa; rw [if_pos hpb] at h; omega
      · exact cnt_le_one (by split_ifs at h <;> omega) ha' hb' hpa hpb

/-- A gate reads at most two wires. -/
theorem not_reads_three (g : Gate) {u v w : ℕ} (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hu : g.a.Reads u ∨ g.b.Reads u) (hv : g.a.Reads v ∨ g.b.Reads v)
    (hw : g.a.Reads w ∨ g.b.Reads w) : False := by
  obtain ⟨a, b⟩ := g
  cases a <;> cases b <;> simp only [Ref.Reads, false_or, or_false] at hu hv hw <;> omega

theorem Ref.readsConst_of_reads {n z : ℕ} {c : Bool} (hz : z < n) (rgs : List Gate) (r : Ref)
    (h : r.Reads z) : r.ReadsConst n z c rgs := by
  cases r with
  | const _ => simp [Ref.Reads] at h
  | wire w neg =>
      simp only [Ref.Reads] at h; subst h
      exact ⟨c, fun x => by rw [val_input n _ rgs w hz, upd_same]⟩

/-- The cascade under `z := c`, when the restriction makes the first gate `0`, contains the first gate and
every later gate that reads `z` or the first gate. -/
theorem cascade_first (n z : ℕ) (c : Bool) (hz : z < n) (g0 : Gate)
    (h0 : g0.a.Reads z ∨ g0.b.Reads z) (hf : ∀ x, g0.eval (val n (upd x z c) []) = false) :
    ∀ later : List Gate,
      1 + cnt (fun g => (g.a.Reads z ∨ g.b.Reads z) ∨ (g.a.Reads n ∨ g.b.Reads n)) later ≤
        cascade n z c (later ++ [g0])
  | [] => by
      have hc : g0.a.ReadsConst n z c [] ∨ g0.b.ReadsConst n z c [] :=
        h0.imp (fun h => Ref.readsConst_of_reads (c := c) hz [] _ h)
          (fun h => Ref.readsConst_of_reads (c := c) hz [] _ h)
      simp only [List.nil_append, cascade, cnt, if_pos hc]
      omega
  | g :: later => by
      have ih := cascade_first n z c hz g0 h0 hf later
      have hn : ∀ r : Ref, r.Reads n → r.ReadsConst n z c (later ++ [g0]) := by
        intro r hr
        cases r with
        | const _ => simp [Ref.Reads] at hr
        | wire w neg =>
            simp only [Ref.Reads] at hr
            refine ⟨false, fun x => ?_⟩
            show val n (upd x z c) (later ++ [g0]) w = false
            rw [hr, val_append_lt n _ [g0] later n (by simp)]
            show (if n = n + ([] : List Gate).length then g0.eval (val n (upd x z c) [])
              else val n (upd x z c) [] n) = false
            rw [if_pos (by simp)]
            exact hf x
      simp only [List.cons_append, cascade, cnt]
      by_cases hp : (g.a.Reads z ∨ g.b.Reads z) ∨ (g.a.Reads n ∨ g.b.Reads n)
      · have hc : g.a.ReadsConst n z c (later ++ [g0]) ∨ g.b.ReadsConst n z c (later ++ [g0]) := by
          rcases hp with (h | h) | (h | h)
          · exact Or.inl (Ref.readsConst_of_reads (c := c) hz _ _ h)
          · exact Or.inr (Ref.readsConst_of_reads (c := c) hz _ _ h)
          · exact Or.inl (hn _ h)
          · exact Or.inr (hn _ h)
        rw [if_pos hp, if_pos hc]
        omega
      · rw [if_neg hp]
        split_ifs <;> omega

/-! ## The lower bound -/

/-- **XNOR conjunction lower bound.** Every free-NOT AIG for the AND of `|P|` XNORs on disjoint pairs of
inputs has at least `4 |P| - 1` gates. -/
theorem xnorConj_lower (n : ℕ) : ∀ (k : ℕ) (P : List (ℕ × ℕ)), P.length = k →
    (∀ p ∈ P, p.1 < n ∧ p.2 < n) → PairsNodup P →
    ∀ C : Circuit, C.n = n → (∀ x, C.eval x = xnorConj P x) → 4 * P.length ≤ C.size + 1 := by
  intro k
  induction k with
  | zero => intro P hk _ _ C _ _; omega
  | succ k ihk =>
    intro P hk hlt hnd
    suffices H : ∀ s, ∀ C : Circuit, C.size = s → C.n = n → (∀ x, C.eval x = xnorConj P x) →
        4 * P.length ≤ C.size + 1 from fun C hn hf => H _ C rfl hn hf
    intro s
    induction s using Nat.strong_induction_on with
    | _ s ihs =>
    intro C hs hn hf
    -- a smaller circuit for the same function suffices
    have small : ∀ C' : Circuit, C'.n = n → C'.size < C.size → (∀ x, C'.eval x = C.eval x) →
        4 * P.length ≤ C.size + 1 := fun C' hn' hlt' he => by
      have := ihs C'.size (hs ▸ hlt') C' rfl hn' (fun x => (he x).trans (hf x))
      omega
    obtain ⟨p0, hp0⟩ : ∃ p, p ∈ P := List.exists_mem_of_length_pos (by omega)
    have hne0 := (pair_facts hnd hp0).1
    have hs1 : Supp P p0.1 := ⟨p0, hp0, Or.inl rfl⟩
    have hs2 : Supp P p0.2 := ⟨p0, hp0, Or.inr rfl⟩
    rcases List.eq_nil_or_concat C.rgates with hnil | ⟨later, g0, hC⟩
    all_goals try rw [List.concat_eq_append] at hC
    · -- no gates: the output reads at most one of the two inputs of `p0`
      exfalso
      have hign : ∀ t, t < n → ¬ C.out.Reads t → ∀ x b, C.eval (upd x t b) = C.eval x :=
        fun t ht ho x b => Circuit.eval_upd_of_not_reads C t b (hn ▸ ht)
          (by rw [hnil]; simp) ho x
      by_cases ho : C.out.Reads p0.1
      · have ho2 : ¬ C.out.Reads p0.2 := by
          cases h : C.out with
          | const _ => simp [Ref.Reads]
          | wire w _ => rw [h] at ho; simp only [Ref.Reads] at ho ⊢; omega
        exact not_ignores P hnd _ hs2 C.eval hf (hign _ (hlt p0 hp0).2 ho2)
      · exact not_ignores P hnd _ hs1 C.eval hf (hign _ (hlt p0 hp0).1 ho)
    rcases first_gate_cases n g0 with hdeg | ⟨u, nu, v, nv, rfl, hu, hv, huv⟩
    · -- a degenerate first gate is bypassed
      obtain ⟨L, hL⟩ := hdeg
      obtain ⟨C', hn', hs', he⟩ := bypass C later [] _ L hC (fun x => by rw [hn]; exact hL x)
      exact small C' (hn'.trans hn) (by omega) he
    have hg0 : ∀ y, (Gate.mk (.wire u nu) (.wire v nv)).eval y =
        (Bool.xor (y u) nu && Bool.xor (y v) nv) := fun y => rfl
    have hg0' : ∀ y, (Gate.mk (.wire u nu) (.wire v nv)).eval y =
        (Bool.xor (y v) nv && Bool.xor (y u) nu) := fun y => Bool.and_comm _ _
    have hmem0 : Gate.mk (.wire u nu) (.wire v nv) ∈ C.rgates := by rw [hC]; simp
    -- both inputs of the first gate belong to the pairs
    have hsupp : ∀ t, t < n → (Gate.mk (.wire u nu) (.wire v nv)).a.Reads t ∨
        (Gate.mk (.wire u nu) (.wire v nv)).b.Reads t → Supp P t ∨ 4 * P.length ≤ C.size + 1 := by
      intro t ht hr
      by_cases hst : Supp P t
      · exact Or.inl hst
      · right
        obtain ⟨C', hn', hs', he⟩ := restrict_eliminates C t false (hn ▸ ht)
        have := one_le_readers hmem0 hr
        exact small C' (hn'.trans hn) (by omega) (fun x => by
          rw [he, hf, hf, xnorConj_upd_of_not_supp P t hst])
    rcases hsupp u hu (Or.inl rfl) with hsu | hdone
    swap; · exact hdone
    rcases hsupp v hv (Or.inr rfl) with hsv | hdone
    swap; · exact hdone
    -- second readers of `u` and `v`
    obtain ⟨gv, hgv, hrv⟩ := second_reader hnd C hn hf later _ hC hu hv huv hsu hsv hg0
    obtain ⟨gu, hgu, hru⟩ := second_reader hnd C hn hf later _ hC hv hu (Ne.symm huv) hsv hsu hg0'
    -- the first gate is not the output and has a reader
    have hnot_out : ¬ C.out.Reads n := by
      intro ho
      cases hout : C.out with
      | const _ => rw [hout] at ho; simp [Ref.Reads] at ho
      | wire w neg =>
          rw [hout] at ho; simp only [Ref.Reads] at ho
          have key : ∀ y, C.eval y = Bool.xor (Bool.xor (y u) nu && Bool.xor (y v) nv) neg := by
            intro y
            simp only [Circuit.eval, hout, Ref.eval, hC, hn, ho]
            rw [val_append_lt n y [Gate.mk (.wire u nu) (.wire v nv)] later n (by simp)]
            simp [val, Gate.eval, Ref.eval, val_input, hu, hv]
          have e1 := key (fun _ => nu)
          have e2 := key (upd (fun _ => nu) v (!nu))
          rw [hf, xnorConj_const] at e1
          rw [hf, xnorConj_flip P hnd v hsv nu] at e2
          cases neg <;> simp [upd, huv] at e1 e2
    by_cases hdead : ∃ g ∈ later, g.a.Reads n ∨ g.b.Reads n
    swap
    · simp only [not_exists, not_and, not_or] at hdead
      obtain ⟨C', hn', hs', he⟩ := delete_dead C later [] _ hC (by simpa [hn] using hdead)
        (by simpa [hn] using hnot_out)
      exact small C' (hn'.trans hn) (by omega) he
    obtain ⟨gn, hgn, hrn⟩ := hdead
    -- choose `z ∈ {u, v}` with two later gates reading `z` or the first gate
    have hun : u ≠ n := by omega
    have hvn : v ≠ n := by omega
    have pick : ∃ z c, z < n ∧ Supp P z ∧
        ((Gate.mk (.wire u nu) (.wire v nv)).a.Reads z ∨ (Gate.mk (.wire u nu) (.wire v nv)).b.Reads z) ∧
        (∀ x, (Gate.mk (.wire u nu) (.wire v nv)).eval (val n (upd x z c) []) = false) ∧
        2 ≤ cnt (fun g => (g.a.Reads z ∨ g.b.Reads z) ∨ (g.a.Reads n ∨ g.b.Reads n)) later := by
      by_cases hcu : 2 ≤ cnt (fun g => (g.a.Reads u ∨ g.b.Reads u) ∨ (g.a.Reads n ∨ g.b.Reads n)) later
      · refine ⟨u, nu, hu, hsu, Or.inl rfl, fun x => ?_, hcu⟩
        rw [hg0, val_input n _ [] u hu]; simp
      by_cases hcv : 2 ≤ cnt (fun g => (g.a.Reads v ∨ g.b.Reads v) ∨ (g.a.Reads n ∨ g.b.Reads n)) later
      · refine ⟨v, nv, hv, hsv, Or.inr rfl, fun x => ?_, hcv⟩
        rw [hg0, val_input n _ [] v hv]; simp
      exfalso
      have e1 := cnt_le_one (p := fun g => (g.a.Reads u ∨ g.b.Reads u) ∨ (g.a.Reads n ∨ g.b.Reads n))
        (by omega) hgu hgn (Or.inl hru) (Or.inr hrn)
      have e2 := cnt_le_one (p := fun g => (g.a.Reads v ∨ g.b.Reads v) ∨ (g.a.Reads n ∨ g.b.Reads n))
        (by omega) hgv hgn (Or.inl hrv) (Or.inr hrn)
      subst e1
      exact not_reads_three gu huv hun hvn hru (e2 ▸ hrv) hrn
    obtain ⟨z, c, hz, hsz, hrz, hfz, hcz⟩ := pick
    have hcas := cascade_first n z c hz _ hrz hfz later
    obtain ⟨C', hn', hs', he', -⟩ := cascade_restriction C z c (hn ▸ hz)
    rw [hC, hn] at hs'
    obtain ⟨p, hp, z', hz', hnz', hres⟩ := xnorConj_restrict P hnd hlt z hsz
    have hlen : (P.erase p).length = k := by rw [List.length_erase_of_mem hp]; omega
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · -- one pair: three gates suffice
      omega
    -- the restriction is `xnorConj (P.erase p) ∧ (x_z' == c)`; peel the literal
    obtain ⟨q, hq⟩ : ∃ q, q ∈ P.erase p := List.exists_mem_of_length_pos (by omega)
    obtain ⟨-, -, -, hnd'⟩ := pair_facts hnd hp
    have hR : Realizes n (fun x => xnorConj (P.erase p) x && (x z' == c)) C'.size :=
      ⟨C', hn'.trans hn, le_rfl, fun x => by rw [he', hf, hres]⟩
    obtain ⟨C'', hn'', hs'', hf''⟩ := literal_extension_phase hz' c _
      (fun x d => xnorConj_upd_of_not_supp _ z' hnz' x d)
      ⟨fun _ => false, xnorConj_const _ false⟩
      ⟨_, xnorConj_flip _ hnd' q.1 ⟨q, hq, Or.inl rfl⟩ false⟩ hR
    have := ihk (P.erase p) hlen (fun r hr => hlt r (List.mem_of_mem_erase hr)) hnd' C'' hn'' hf''
    omega

/-! ## The standard pairs -/

/-- The pairs `(2j, 2j+1)` for `j < q`. -/
def stdPairs (q : ℕ) : List (ℕ × ℕ) := (List.range q).map fun j => (2 * j, 2 * j + 1)

theorem stdPairs_flat_lt (q : ℕ) : ∀ w ∈ (stdPairs q).flatMap (fun p => [p.1, p.2]), w < 2 * q := by
  intro w hw
  simp only [stdPairs, List.flatMap_map, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hw
  obtain ⟨j, hj, h⟩ := hw
  omega

theorem stdPairs_nodup (q : ℕ) : PairsNodup (stdPairs q) := by
  induction q with
  | zero => simp [PairsNodup, stdPairs]
  | succ q ih =>
      have hlt := stdPairs_flat_lt q
      unfold PairsNodup stdPairs at *
      rw [List.range_succ, List.map_append, List.flatMap_append, List.nodup_append]
      refine ⟨ih, by simp, ?_⟩
      intro a ha b hb
      have := hlt a ha
      simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.mem_cons, List.not_mem_nil, or_false] at hb
      omega

/-- **`C(F_q) ≥ 4q - 1`.** Every free-NOT AIG on `n ≥ 2q` inputs for `∧_{j<q} (x_{2j} == x_{2j+1})`
has at least `4q - 1` gates. -/
theorem xnorConj_std_lower {n q s : ℕ} (hq : 2 * q ≤ n) (h : Realizes n (xnorConj (stdPairs q)) s) :
    4 * q ≤ s + 1 := by
  obtain ⟨C, hn, hs, hf⟩ := h
  have := xnorConj_lower n q (stdPairs q) (by simp [stdPairs])
    (fun p hp => by
      simp only [stdPairs, List.mem_map, List.mem_range] at hp
      obtain ⟨j, hj, rfl⟩ := hp
      exact ⟨by dsimp only; omega, by dsimp only; omega⟩)
    (stdPairs_nodup q) C hn hf
  simp only [stdPairs, List.length_map, List.length_range] at this
  omega

end CircuitLemmas.GateElim
