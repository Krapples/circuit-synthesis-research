/-
Strong pair sensitivity and the three-gate step (2026-11-26).

`Strong f S`: for distinct `u, v ∈ S` and every `c`, the restriction `f|_{u=c}` still depends on `v`.

* `three_step`: if `f` is `Strong` on a set `S` of at least two inputs and ignores every input outside `S`,
  then some `z ∈ S` and `c` satisfy `C(f|_{z=c}) ≤ C(f) - 3` (and `C(f) ≥ 3`).
* `potential_lower`: a potential that drops by one along such restrictions (up to free extra fixing) gives
  `C(f) ≥ 3μ`.
* `potential_restriction_lower`: combined with `excess_restriction`, `C(f) ≥ |F| + 3μ`.

This is the gate-elimination core of the robust-identifier `2n - o(n)` argument for `SAT`, in a form that
does not use the additive-weight theorem. The SAT-specific premises are not formalized here.
-/
import CircuitLemmas.XnorConj
import CircuitLemmas.Excess

namespace CircuitLemmas.GateElim

/-- `f` depends on input `v`. -/
def Dep (f : (ℕ → Bool) → Bool) (v : ℕ) : Prop := ∃ x, f (upd x v true) ≠ f (upd x v false)

/-- **Strong pair sensitivity.** Fixing any one input of `S` leaves every other input of `S` relevant. -/
def Strong (f : (ℕ → Bool) → Bool) (S : Set ℕ) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ∀ c, Dep (fun x => f (upd x u c)) v

theorem upd_comm (x : ℕ → Bool) {i j : ℕ} (h : i ≠ j) (b c : Bool) :
    upd (upd x i b) j c = upd (upd x j c) i b := by
  funext w
  by_cases hi : w = i
  · subst hi; simp [upd, h]
  · by_cases hj : w = j
    · subst hj; simp [upd, hi]
    · simp [upd, hi, hj]

theorem strong_contra {f : (ℕ → Bool) → Bool} {S : Set ℕ} (hS : Strong f S) {u v : ℕ}
    (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v) (c : Bool)
    (h : ∀ y b, f (upd (upd y u c) v b) = f (upd y u c)) : False := by
  obtain ⟨x, hx⟩ := hS u hu v hv huv c
  apply hx
  show f (upd (upd x v true) u c) = f (upd (upd x v false) u c)
  rw [upd_comm x (Ne.symm huv) true c, upd_comm x (Ne.symm huv) false c, h, h]

/-- A `Strong` function ignores no input of `S` (when `S` has another element). -/
theorem strong_ignores {f : (ℕ → Bool) → Bool} {S : Set ℕ} (hS : Strong f S) {u v : ℕ}
    (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v) (h : ∀ x b, f (upd x v b) = f x) : False :=
  strong_contra hS hu hv huv false fun _ b => h _ b

/-- **Second reader.** In a circuit for a `Strong` function whose first gate is `l_u ∧ l_v`, some later
gate reads `v`. -/
theorem strong_second_reader {n : ℕ} {f : (ℕ → Bool) → Bool} {S : Set ℕ} (hS : Strong f S)
    (C : Circuit) (hn : C.n = n) (hf : ∀ x, C.eval x = f x) (later : List Gate) (g0 : Gate)
    (hC : C.rgates = later ++ [g0]) {u v : ℕ} {nu nv : Bool} (hu : u < n) (hv : v < n) (huv : u ≠ v)
    (hsu : u ∈ S) (hsv : v ∈ S)
    (hg0 : ∀ y, g0.eval y = (Bool.xor (y u) nu && Bool.xor (y v) nv)) :
    ∃ g ∈ later, g.a.Reads v ∨ g.b.Reads v := by
  by_contra hno
  simp only [not_exists, not_and, not_or] at hno
  by_cases ho : C.out.Reads v
  · -- the output is the literal `x_v`, which ignores `x_u`
    apply strong_ignores hS hsv hsu (Ne.symm huv)
    intro x b
    rw [← hf, ← hf]
    have hvC : v < C.n := hn ▸ hv
    cases hout : C.out with
    | const _ => rw [hout] at ho; simp [Ref.Reads] at ho
    | wire w neg =>
        rw [hout] at ho; simp only [Ref.Reads] at ho; subst ho
        simp only [Circuit.eval, hout, Ref.eval, val_input C.n _ C.rgates w hvC, upd,
          if_neg (Ne.symm huv)]
  · -- only `g0` reads `v`; with `l_u` false the circuit ignores `x_v`
    apply strong_contra hS hsu hsv huv nu
    intro y b
    rw [← hf, ← hf]
    exact eval_flip_first C later g0 hC v hno ho (upd y u nu) b (by
      rw [hg0, hg0, val_input C.n _ [] u (hn ▸ hu), val_input C.n _ [] u (hn ▸ hu)]
      simp [upd, huv])

/-- **Three-gate step.** If `f` is `Strong` on `S ⊆ [0, n)`, ignores every input outside `S`, and `S` has
two distinct elements, then every circuit for `f` has at least three gates and some restriction
`z := c` with `z ∈ S` has a circuit with three fewer gates. -/
theorem three_step {n : ℕ} {f : (ℕ → Bool) → Bool} {S : Set ℕ} (hS : Strong f S)
    (hSn : ∀ t ∈ S, t < n) (hout : ∀ t, t ∉ S → ∀ x b, f (upd x t b) = f x)
    {u0 v0 : ℕ} (hu0 : u0 ∈ S) (hv0 : v0 ∈ S) (huv0 : u0 ≠ v0) :
    ∀ C : Circuit, C.n = n → (∀ x, C.eval x = f x) →
      ∃ z ∈ S, ∃ c, Realizes n (fun x => f (upd x z c)) (C.size - 3) ∧ 3 ≤ C.size := by
  suffices H : ∀ s, ∀ C : Circuit, C.size = s → C.n = n → (∀ x, C.eval x = f x) →
      ∃ z ∈ S, ∃ c, Realizes n (fun x => f (upd x z c)) (C.size - 3) ∧ 3 ≤ C.size from
    fun C hn hf => H _ C rfl hn hf
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ihs =>
  intro C hs hn hf
  -- a smaller circuit for the same function suffices
  have small : ∀ C' : Circuit, C'.n = n → C'.size < C.size → (∀ x, C'.eval x = C.eval x) →
      ∃ z ∈ S, ∃ c, Realizes n (fun x => f (upd x z c)) (C.size - 3) ∧ 3 ≤ C.size := by
    intro C' hn' hlt' he
    obtain ⟨z, hz, c, ⟨D, hDn, hDs, hDf⟩, h3⟩ :=
      ihs C'.size (hs ▸ hlt') C' rfl hn' (fun x => (he x).trans (hf x))
    exact ⟨z, hz, c, ⟨D, hDn, by omega, hDf⟩, by omega⟩
  rcases List.eq_nil_or_concat C.rgates with hnil | ⟨later, g0, hC⟩
  all_goals try rw [List.concat_eq_append] at hC
  · -- no gates: the output ignores one of `u0, v0`
    exfalso
    have hign : ∀ t, t < n → ¬ C.out.Reads t → ∀ x b, f (upd x t b) = f x := by
      intro t ht ho x b
      rw [← hf, ← hf]
      exact Circuit.eval_upd_of_not_reads C t b (hn ▸ ht) (by rw [hnil]; simp) ho x
    by_cases ho : C.out.Reads u0
    · have ho2 : ¬ C.out.Reads v0 := by
        cases h : C.out with
        | const _ => simp [Ref.Reads]
        | wire w _ => rw [h] at ho; simp only [Ref.Reads] at ho ⊢; omega
      exact strong_ignores hS hu0 hv0 huv0 (hign _ (hSn _ hv0) ho2)
    · exact strong_ignores hS hv0 hu0 (Ne.symm huv0) (hign _ (hSn _ hu0) ho)
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
  -- both inputs of the first gate lie in `S`; otherwise fixing one deletes the first gate
  by_cases hsu : u ∈ S
  swap
  · obtain ⟨C', hn', hs', he⟩ := restrict_eliminates C u false (hn ▸ hu)
    have := one_le_readers hmem0 (Or.inl rfl)
    exact small C' (hn'.trans hn) (by omega) (fun x => by rw [he, hf, hf, hout u hsu])
  by_cases hsv : v ∈ S
  swap
  · obtain ⟨C', hn', hs', he⟩ := restrict_eliminates C v false (hn ▸ hv)
    have := one_le_readers hmem0 (Or.inr rfl)
    exact small C' (hn'.trans hn) (by omega) (fun x => by rw [he, hf, hf, hout v hsv])
  -- second readers of `u` and `v`
  obtain ⟨gv, hgv, hrv⟩ := strong_second_reader hS C hn hf later _ hC hu hv huv hsu hsv hg0
  obtain ⟨gu, hgu, hru⟩ := strong_second_reader hS C hn hf later _ hC hv hu (Ne.symm huv) hsv hsu hg0'
  -- the first gate is not the output
  have hnot_out : ¬ C.out.Reads n := by
    intro ho
    cases hout' : C.out with
    | const _ => rw [hout'] at ho; simp [Ref.Reads] at ho
    | wire w neg =>
        rw [hout'] at ho; simp only [Ref.Reads] at ho
        have key : ∀ y, C.eval y = Bool.xor (Bool.xor (y u) nu && Bool.xor (y v) nv) neg := by
          intro y
          simp only [Circuit.eval, hout', Ref.eval, hC, hn, ho]
          rw [val_append_lt n y [Gate.mk (.wire u nu) (.wire v nv)] later n (by simp)]
          simp [val, Gate.eval, Ref.eval, hu, hv]
        apply strong_contra hS hsu hsv huv nu
        intro y b
        rw [← hf, ← hf, key, key]
        simp [upd, huv]
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
  have pick : ∃ z c, z < n ∧ z ∈ S ∧
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
  exact ⟨z, hsz, c, ⟨C', hn'.trans hn, by omega, fun x => by rw [he', hf]⟩, by omega⟩

/-- **Potential bound.** Suppose that whenever `P f (m + 1)` holds, `f` is `Strong` on a set `S` of at least
two inputs below `n`, ignores every input outside `S`, and every restriction `z := c` with `z ∈ S` can be
completed for free (by a further restriction that does not increase size) to a function `g` with
`P g m`. Then `P f m` implies `C(f) ≥ 3m`. -/
theorem potential_lower {n : ℕ} (P : ((ℕ → Bool) → Bool) → ℕ → Prop)
    (hstep : ∀ f m, P f (m + 1) → ∃ S : Set ℕ, Strong f S ∧ (∀ t ∈ S, t < n) ∧
      (∀ t, t ∉ S → ∀ x b, f (upd x t b) = f x) ∧ (∃ u ∈ S, ∃ v ∈ S, u ≠ v) ∧
      ∀ z ∈ S, ∀ c s, Realizes n (fun x => f (upd x z c)) s → ∃ g, P g m ∧ Realizes n g s) :
    ∀ m f s, P f m → Realizes n f s → 3 * m ≤ s := by
  intro m
  induction m with
  | zero => intros; omega
  | succ m ih =>
    intro f s hP hR
    obtain ⟨S, hS, hSn, hout, ⟨u, hu, v, hv, huv⟩, hcl⟩ := hstep f m hP
    obtain ⟨C, hn, hs, hf⟩ := hR
    obtain ⟨z, hz, c, hR', h3⟩ := three_step hS hSn hout hu hv huv C hn hf
    obtain ⟨g, hg, hRg⟩ := hcl z hz c _ hR'
    have := ih g _ hg hRg
    omega

/-- **Restriction plus potential.** If fixing a set `F` of essential inputs leaves a function of potential
`m ≥ 1`, then `C(f) ≥ |F| + 3m`. -/
theorem potential_restriction_lower {n s m : ℕ} {f : (ℕ → Bool) → Bool}
    (P : ((ℕ → Bool) → Bool) → ℕ → Prop)
    (hstep : ∀ f m, P f (m + 1) → ∃ S : Set ℕ, Strong f S ∧ (∀ t ∈ S, t < n) ∧
      (∀ t, t ∉ S → ∀ x b, f (upd x t b) = f x) ∧ (∃ u ∈ S, ∃ v ∈ S, u ≠ v) ∧
      ∀ z ∈ S, ∀ c s, Realizes n (fun x => f (upd x z c)) s → ∃ g, P g m ∧ Realizes n g s)
    (F : Finset ℕ) (b : ℕ → Bool) (hFn : ∀ z ∈ F, z < n)
    (hess : ∀ z ∈ F, ∃ x, f (upd x z true) ≠ f (upd x z false))
    (hm : 1 ≤ m) (hP : P (fun x => f (fixS F b x)) m) (h : Realizes n f s) :
    F.card + 3 * m ≤ s := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hnc : ∃ x y, f (fixS F b x) ≠ f (fixS F b y) := by
    obtain ⟨S, hS, -, -, ⟨u, hu, v, hv, huv⟩, -⟩ := hstep _ m' hP
    by_contra hc
    simp only [not_exists, not_not] at hc
    exact strong_ignores hS hu hv huv fun x c => hc _ _
  have h1 := excess_restriction F b hFn hess hnc h
  have h2 := potential_lower P hstep _ _ _ hP h1
  omega

end CircuitLemmas.GateElim
