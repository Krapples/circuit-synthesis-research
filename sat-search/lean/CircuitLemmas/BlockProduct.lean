/-
Products of pair-sensitive blocks (2026-11-26).

A factor `φ` on a block `V` is `PS d` (pair-sensitive at level `d`) if every partial assignment that leaves
at least `d` inputs of `V` free leaves a `Strong` function on those free inputs. For an AND of `PS d`
factors (`d ≥ 2`) on pairwise disjoint blocks:

* `block_product_lower`: `C(∧_j φ_j) ≥ 3 · Σ_j (|V_j| - d + 1)` when every block has at least `d` inputs;
* `block_restriction_lower`: if fixing a set `F` of essential inputs of `f` leaves such a product, then
  `C(f) ≥ |F| + 3 · Σ_j (|V_j| - d + 1)`.

Proof: `potential_lower` with the potential `Σ_j max(0, free_j - d + 1)`. Fixing an input of an active block
lowers it by one; when a block falls to `d - 1` free inputs it is still satisfiable, and its remaining inputs
are fixed to a satisfying assignment for free.

This is the gate-elimination part of the robust-identifier `2n - o(n)` argument for `SAT`, without the
additive-weight theorem. The existence of `PS d` factors and the SAT restriction identities are not
formalized here.
-/
import CircuitLemmas.Robust

namespace CircuitLemmas.GateElim

/-- Apply a partial assignment. -/
def fixP (ρ : ℕ → Option Bool) (x : ℕ → Bool) : ℕ → Bool := fun w => (ρ w).getD (x w)

/-- `φ` depends only on the inputs in `V`. -/
def DepOn (V : Finset ℕ) (φ : (ℕ → Bool) → Bool) : Prop :=
  ∀ x y, (∀ w ∈ V, x w = y w) → φ x = φ y

/-- The inputs of `V` left free by `ρ`. -/
def freeIn (V : Finset ℕ) (ρ : ℕ → Option Bool) : Finset ℕ := V.filter fun w => ρ w = none

/-- **Pair sensitivity at level `d`.** -/
def PS (d : ℕ) (V : Finset ℕ) (φ : (ℕ → Bool) → Bool) : Prop :=
  ∀ ρ, d ≤ (freeIn V ρ).card → Strong (fun x => φ (fixP ρ x)) (↑(freeIn V ρ) : Set ℕ)

def setP (ρ : ℕ → Option Bool) (u : ℕ) (c : Bool) : ℕ → Option Bool :=
  fun w => if w = u then some c else ρ w

def fill (ρ : ℕ → Option Bool) (D : Finset ℕ) (σ : ℕ → Bool) : ℕ → Option Bool :=
  fun w => if w ∈ D then some (σ w) else ρ w

/-- The AND of the first `k` factors. -/
def prodP (k : ℕ) (φ : ℕ → (ℕ → Bool) → Bool) (y : ℕ → Bool) : Bool := (List.range k).all fun j => φ j y

/-- Every block is active (at least `d` free inputs) or fully fixed with value `true`. -/
def Inv (k d : ℕ) (V : ℕ → Finset ℕ) (φ : ℕ → (ℕ → Bool) → Bool) (ρ : ℕ → Option Bool) : Prop :=
  ∀ j < k, d ≤ (freeIn (V j) ρ).card ∨ (freeIn (V j) ρ = ∅ ∧ ∀ x, φ j (fixP ρ x) = true)

/-- The potential `Σ_j max(0, free_j + 1 - d)`. -/
def mu (k d : ℕ) (V : ℕ → Finset ℕ) (ρ : ℕ → Option Bool) : ℕ :=
  (Finset.range k).sum fun j => (freeIn (V j) ρ).card + 1 - d

/-! ## Basic facts -/

theorem mem_freeIn {V : Finset ℕ} {ρ : ℕ → Option Bool} {w : ℕ} :
    w ∈ freeIn V ρ ↔ w ∈ V ∧ ρ w = none := Finset.mem_filter

theorem dep_sat {F : (ℕ → Bool) → Bool} {w : ℕ} (h : Dep F w) : ∃ σ, F σ = true := by
  obtain ⟨x, hx⟩ := h
  cases e : F (upd x w true)
  · exact ⟨upd x w false, by rw [e] at hx; cases e' : F (upd x w false) <;> simp_all⟩
  · exact ⟨_, e⟩

theorem fixP_congr_on {V : Finset ℕ} {φ : (ℕ → Bool) → Bool} (hd : DepOn V φ) (ρ : ℕ → Option Bool)
    {x y : ℕ → Bool} (hxy : ∀ w ∈ V, x w = y w) : φ (fixP ρ x) = φ (fixP ρ y) :=
  hd _ _ fun w hw => by simp only [fixP, hxy w hw]

theorem fixP_upd_not_free {V : Finset ℕ} {φ : (ℕ → Bool) → Bool} (hd : DepOn V φ) (ρ : ℕ → Option Bool)
    {t : ℕ} (ht : t ∉ freeIn V ρ) (x : ℕ → Bool) (b : Bool) : φ (fixP ρ (upd x t b)) = φ (fixP ρ x) := by
  apply hd
  intro w hw
  simp only [fixP, upd]
  by_cases hwt : w = t
  · rw [if_pos hwt]
    rw [hwt] at hw ⊢
    cases hρ : ρ t with
    | none => exact absurd (Finset.mem_filter.mpr ⟨hw, hρ⟩) ht
    | some c => rfl
  · rw [if_neg hwt]

theorem fixP_upd (ρ : ℕ → Option Bool) {u : ℕ} (hu : ρ u = none) (c : Bool) (x : ℕ → Bool) :
    fixP ρ (upd x u c) = fixP (setP ρ u c) x := by
  funext w
  by_cases h : w = u
  · subst h; simp [fixP, setP, upd, hu]
  · simp [fixP, setP, upd, h]

theorem freeIn_setP (V : Finset ℕ) (ρ : ℕ → Option Bool) (u : ℕ) (c : Bool) :
    freeIn V (setP ρ u c) = (freeIn V ρ).erase u := by
  ext w
  simp only [freeIn, Finset.mem_filter, Finset.mem_erase]
  by_cases h : w = u <;> simp [setP, h]

theorem freeIn_setP_of_not_mem {V : Finset ℕ} (ρ : ℕ → Option Bool) {u : ℕ} (hu : u ∉ V) (c : Bool) :
    freeIn V (setP ρ u c) = freeIn V ρ := by
  ext w
  simp only [freeIn, Finset.mem_filter]
  by_cases h : w = u
  · subst h; simp [setP, hu]
  · simp [setP, h]

theorem fixP_fill (ρ : ℕ → Option Bool) (D : Finset ℕ) (σ : ℕ → Bool) (hD : ∀ w ∈ D, ρ w = none)
    (x : ℕ → Bool) : fixP (fill ρ D σ) x = fixP ρ (fixS D σ x) := by
  funext w
  by_cases hw : w ∈ D
  · simp [fixP, fill, fixS, hw, hD w hw]
  · simp [fixP, fill, fixS, hw]

theorem freeIn_fill_self (V : Finset ℕ) (ρ : ℕ → Option Bool) (σ : ℕ → Bool) :
    freeIn V (fill ρ (freeIn V ρ) σ) = ∅ := by
  ext w
  rw [mem_freeIn]
  simp only [fill]
  constructor
  · rintro ⟨hw, he⟩
    by_cases hf : w ∈ freeIn V ρ
    · rw [if_pos hf] at he; exact absurd he (by simp)
    · rw [if_neg hf] at he; exact absurd (mem_freeIn.mpr ⟨hw, he⟩) hf
  · intro h; simp at h

theorem freeIn_fill_of_disj (V : Finset ℕ) (ρ : ℕ → Option Bool) (D : Finset ℕ) (σ : ℕ → Bool)
    (hVD : ∀ w ∈ V, w ∉ D) : freeIn V (fill ρ D σ) = freeIn V ρ := by
  ext w
  rw [mem_freeIn, mem_freeIn]
  simp only [fill]
  constructor
  · rintro ⟨hw, he⟩; rw [if_neg (hVD w hw)] at he; exact ⟨hw, he⟩
  · rintro ⟨hw, he⟩; rw [if_neg (hVD w hw)]; exact ⟨hw, he⟩

theorem fill_agree (V : Finset ℕ) (ρ : ℕ → Option Bool) (σ x : ℕ → Bool) :
    ∀ w ∈ V, fixP (fill ρ (freeIn V ρ) σ) x w = fixP ρ σ w := by
  intro w hw
  by_cases hf : w ∈ freeIn V ρ
  · have hn : ρ w = none := (Finset.mem_filter.mp hf).2
    simp [fixP, fill, hf, hn]
  · simp only [fixP, fill, if_neg hf]
    cases hρ : ρ w with
    | none => exact absurd (Finset.mem_filter.mpr ⟨hw, hρ⟩) hf
    | some c => rfl

theorem prodP_eq (k : ℕ) (φ : ℕ → (ℕ → Bool) → Bool) (y : ℕ → Bool) (j0 : ℕ) (hj0 : j0 < k)
    (hother : ∀ j < k, j ≠ j0 → φ j y = true) : prodP k φ y = φ j0 y := by
  unfold prodP
  cases hv : φ j0 y with
  | true =>
      rw [List.all_eq_true]
      intro j hj
      by_cases e : j = j0
      · rw [e, hv]
      · exact hother j (List.mem_range.mp hj) e
  | false =>
      cases hb : (List.range k).all (fun j => φ j y)
      · rfl
      · have := (List.all_eq_true.mp hb) j0 (List.mem_range.mpr hj0)
        rw [hv] at this
        exact absurd this (by decide)

theorem prodP_congr {k : ℕ} {φ : ℕ → (ℕ → Bool) → Bool} {y y' : ℕ → Bool}
    (hc : ∀ j < k, φ j y = φ j y') : prodP k φ y = prodP k φ y' := by
  unfold prodP
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  simp only [List.mem_range]
  constructor
  · intro H j hj; rw [← hc j hj]; exact H j hj
  · intro H j hj; rw [hc j hj]; exact H j hj

open Classical in
/-- Glue one assignment per block. -/
noncomputable def merge (k : ℕ) (V : ℕ → Finset ℕ) (σ : ℕ → ℕ → Bool) (w : ℕ) : Bool :=
  if hw : ∃ j, j < k ∧ w ∈ V j then σ (Nat.find hw) w else false

theorem merge_eq {k : ℕ} {V : ℕ → Finset ℕ} (hdisj : ∀ i < k, ∀ j < k, i ≠ j → Disjoint (V i) (V j))
    (σ : ℕ → ℕ → Bool) {j w : ℕ} (hj : j < k) (hw : w ∈ V j) : merge k V σ w = σ j w := by
  have hex : ∃ j, j < k ∧ w ∈ V j := ⟨j, hj, hw⟩
  unfold merge
  rw [dif_pos hex]
  have hs := Nat.find_spec hex
  have e : Nat.find hex = j := by
    by_contra hne
    exact Finset.disjoint_left.mp (hdisj _ hs.1 _ hj hne) hs.2 hw
  rw [e]

theorem merge_agree {k : ℕ} {V : ℕ → Finset ℕ} (hdisj : ∀ i < k, ∀ j < k, i ≠ j → Disjoint (V i) (V j))
    (σ : ℕ → ℕ → Bool) {j : ℕ} (hj : j < k) (v : ℕ) (t : Bool) (u : ℕ) (c : Bool) :
    ∀ w ∈ V j, upd (upd (merge k V σ) v t) u c w = upd (upd (σ j) v t) u c w := by
  intro w hw
  simp only [upd]
  split_ifs
  · rfl
  · rfl
  · exact merge_eq hdisj σ hj hw

theorem sum_change {k i : ℕ} (hi : i < k) (f g : ℕ → ℕ) (hfg : ∀ j < k, j ≠ i → f j = g j) :
    (Finset.range k).sum f + g i = (Finset.range k).sum g + f i := by
  have hmem := Finset.mem_range.mpr hi
  have h1 : f i + ((Finset.range k).erase i).sum f = (Finset.range k).sum f :=
    Finset.add_sum_erase _ f hmem
  have h2 : g i + ((Finset.range k).erase i).sum g = (Finset.range k).sum g :=
    Finset.add_sum_erase _ g hmem
  have hc : ((Finset.range k).erase i).sum f = ((Finset.range k).erase i).sum g :=
    Finset.sum_congr rfl (fun j hj =>
      hfg j (Finset.mem_range.mp (Finset.mem_of_mem_erase hj)) (Finset.ne_of_mem_erase hj))
  omega

theorem realizes_fixS {n s : ℕ} {g : (ℕ → Bool) → Bool} (σ : ℕ → Bool) :
    ∀ D : Finset ℕ, (∀ w ∈ D, w < n) → Realizes n g s → Realizes n (fun x => g (fixS D σ x)) s := by
  intro D
  induction D using Finset.induction_on with
  | empty =>
      intro _ h
      have e : (fun x => g (fixS ∅ σ x)) = g := by
        funext x; congr 1
      rw [e]; exact h
  | @insert a D ha ih =>
      intro hD h
      have h1 := ih (fun w hw => hD w (Finset.mem_insert_of_mem hw)) h
      have h2 := realizes_restrict a (σ a) (hD a (Finset.mem_insert_self a D)) h1
      have e : (fun x => g (fixS (insert a D) σ x)) = fun x => g (fixS D σ (upd x a (σ a))) := by
        funext x; congr 1; funext w
        by_cases hw : w ∈ D <;> by_cases hwa : w = a <;> simp [fixS, upd, hw, hwa]
      rw [e]; exact h2

/-! ## One block -/

theorem block_sat {d : ℕ} {V : Finset ℕ} {φ : (ℕ → Bool) → Bool} (hd2 : 2 ≤ d) (hdep : DepOn V φ)
    (hps : PS d V φ) (ρ : ℕ → Option Bool)
    (hj : d ≤ (freeIn V ρ).card ∨ (freeIn V ρ = ∅ ∧ ∀ x, φ (fixP ρ x) = true)) (u : ℕ) (c : Bool) :
    ∃ σ, φ (fixP ρ (upd σ u c)) = true := by
  rcases hj with hcard | ⟨-, htrue⟩
  swap; · exact ⟨fun _ => false, htrue _⟩
  have hS := hps ρ hcard
  by_cases hu : u ∈ freeIn V ρ
  · obtain ⟨w, hw, hwu⟩ := Finset.exists_mem_ne (by omega : 1 < (freeIn V ρ).card) u
    exact dep_sat (hS u hu w hw (Ne.symm hwu) c)
  · obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < (freeIn V ρ).card)
    obtain ⟨σ, hσ⟩ := dep_sat (hS a ha b hb hab false)
    exact ⟨upd σ a false, by rw [fixP_upd_not_free hdep ρ hu]; exact hσ⟩

theorem block_dep {d : ℕ} {V : Finset ℕ} {φ : (ℕ → Bool) → Bool} (hd2 : 2 ≤ d) (hdep : DepOn V φ)
    (hps : PS d V φ) (ρ : ℕ → Option Bool) (hcard : d ≤ (freeIn V ρ).card) {u v : ℕ}
    (hv : v ∈ freeIn V ρ) (huv : u ≠ v) (c : Bool) :
    ∃ σ, φ (fixP ρ (upd (upd σ v true) u c)) ≠ φ (fixP ρ (upd (upd σ v false) u c)) := by
  have hS := hps ρ hcard
  by_cases hu : u ∈ freeIn V ρ
  · exact hS u hu v hv huv c
  · obtain ⟨w, hw, hwv⟩ := Finset.exists_mem_ne (by omega : 1 < (freeIn V ρ).card) v
    obtain ⟨y, hy⟩ := hS w hw v hv hwv false
    refine ⟨upd y w false, ?_⟩
    rw [fixP_upd_not_free hdep ρ hu, fixP_upd_not_free hdep ρ hu, upd_comm y hwv false true,
      upd_comm y hwv false false]
    exact hy

/-! ## The product -/

/-- Functions of potential at least `m`: products restricted by an invariant partial assignment. -/
def BP (k d : ℕ) (V : ℕ → Finset ℕ) (φ : ℕ → (ℕ → Bool) → Bool) (g : (ℕ → Bool) → Bool) (m : ℕ) : Prop :=
  ∃ ρ, Inv k d V φ ρ ∧ m ≤ mu k d V ρ ∧ ∀ x, g x = prodP k φ (fixP ρ x)

theorem block_hstep {n k d : ℕ} {V : ℕ → Finset ℕ} {φ : ℕ → (ℕ → Bool) → Bool} (hd2 : 2 ≤ d)
    (hVn : ∀ j < k, ∀ w ∈ V j, w < n) (hdisj : ∀ i < k, ∀ j < k, i ≠ j → Disjoint (V i) (V j))
    (hdep : ∀ j < k, DepOn (V j) (φ j)) (hps : ∀ j < k, PS d (V j) (φ j)) :
    ∀ f m, BP k d V φ f (m + 1) → ∃ S : Set ℕ, Strong f S ∧ (∀ t ∈ S, t < n) ∧
      (∀ t, t ∉ S → ∀ x b, f (upd x t b) = f x) ∧ (∃ u ∈ S, ∃ v ∈ S, u ≠ v) ∧
      ∀ z ∈ S, ∀ c s, Realizes n (fun x => f (upd x z c)) s → ∃ g, BP k d V φ g m ∧ Realizes n g s := by
  rintro f m ⟨ρ, hinv, hmu, hf⟩
  have hfe : f = fun x => prodP k φ (fixP ρ x) := funext hf
  subst hfe
  refine ⟨{w | ∃ j < k, d ≤ (freeIn (V j) ρ).card ∧ w ∈ freeIn (V j) ρ}, ?_, ?_, ?_, ?_, ?_⟩
  · -- strong pair sensitivity of the product
    rintro u ⟨ju, hju, hdu, huf⟩ v ⟨jv, hjv, hdv, hvf⟩ huv c
    have hblk : ∀ j, ∃ σ : ℕ → Bool,
        (j = jv → φ j (fixP ρ (upd (upd σ v true) u c)) ≠ φ j (fixP ρ (upd (upd σ v false) u c))) ∧
        (j ≠ jv → j < k → φ j (fixP ρ (upd σ u c)) = true) := by
      intro j
      by_cases hj : j = jv
      · obtain ⟨σ, hσ⟩ := block_dep hd2 (hdep jv hjv) (hps jv hjv) ρ hdv hvf huv c
        exact ⟨σ, fun e => by subst e; exact hσ, fun e => absurd hj e⟩
      · by_cases hjk : j < k
        · obtain ⟨σ, hσ⟩ := block_sat hd2 (hdep j hjk) (hps j hjk) ρ (hinv j hjk) u c
          exact ⟨σ, fun e => absurd e hj, fun _ _ => hσ⟩
        · exact ⟨fun _ => false, fun e => absurd e hj, fun _ h' => absurd h' hjk⟩
    choose σ hσ using hblk
    have hvV : v ∈ V jv := (Finset.mem_filter.mp hvf).1
    have key : ∀ t, prodP k φ (fixP ρ (upd (upd (merge k V σ) v t) u c)) =
        φ jv (fixP ρ (upd (upd (σ jv) v t) u c)) := by
      intro t
      have hoth : ∀ j < k, j ≠ jv → φ j (fixP ρ (upd (upd (merge k V σ) v t) u c)) = true := by
        intro j hj hne
        have hvj : v ∉ freeIn (V j) ρ := fun hm =>
          Finset.disjoint_left.mp (hdisj j hj jv hjv hne) (Finset.mem_filter.mp hm).1 hvV
        rw [fixP_congr_on (hdep j hj) ρ (merge_agree hdisj σ hj v t u c), upd_comm _ (Ne.symm huv),
          fixP_upd_not_free (hdep j hj) ρ hvj]
        exact (hσ j).2 hne hj
      rw [prodP_eq k φ _ jv hjv hoth]
      exact fixP_congr_on (hdep jv hjv) ρ (merge_agree hdisj σ hjv v t u c)
    refine ⟨merge k V σ, ?_⟩
    show prodP k φ (fixP ρ (upd (upd (merge k V σ) v true) u c)) ≠
      prodP k φ (fixP ρ (upd (upd (merge k V σ) v false) u c))
    rw [key, key]
    exact (hσ jv).1 rfl
  · rintro t ⟨j, hj, -, ht⟩
    exact hVn j hj t (Finset.mem_filter.mp ht).1
  · intro t ht x b
    show prodP k φ (fixP ρ (upd x t b)) = prodP k φ (fixP ρ x)
    apply prodP_congr
    intro j hj
    apply fixP_upd_not_free (hdep j hj) ρ
    intro htf
    rcases hinv j hj with hc | ⟨he, -⟩
    · exact ht ⟨j, hj, hc, htf⟩
    · rw [he] at htf; simp at htf
  · have hne : mu k d V ρ ≠ 0 := by omega
    obtain ⟨j, hj, hpos⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    have hjk := Finset.mem_range.mp hj
    have hpos' : (freeIn (V j) ρ).card + 1 - d ≠ 0 := hpos
    have hc : d ≤ (freeIn (V j) ρ).card := by omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < (freeIn (V j) ρ).card)
    exact ⟨a, ⟨j, hjk, hc, ha⟩, b, ⟨j, hjk, hc, hb⟩, hab⟩
  · -- closure under restriction
    rintro z ⟨i, hi, hdi, hzf⟩ c s hR
    have hzn : ρ z = none := (Finset.mem_filter.mp hzf).2
    have hzV : z ∈ V i := (Finset.mem_filter.mp hzf).1
    have hfix1 : ∀ x, fixP ρ (upd x z c) = fixP (setP ρ z c) x := fun x => fixP_upd ρ hzn c x
    have hR1 : Realizes n (fun x => prodP k φ (fixP (setP ρ z c) x)) s := by
      have e : (fun x => prodP k φ (fixP (setP ρ z c) x)) =
          (fun x => (fun x => prodP k φ (fixP ρ x)) (upd x z c)) := by
        funext x; show _ = prodP k φ (fixP ρ (upd x z c)); rw [hfix1]
      rw [e]; exact hR
    have hcard_i : (freeIn (V i) (setP ρ z c)).card + 1 = (freeIn (V i) ρ).card := by
      rw [freeIn_setP, Finset.card_erase_of_mem hzf]; omega
    have hfree_j : ∀ j < k, j ≠ i → freeIn (V j) (setP ρ z c) = freeIn (V j) ρ := fun j hj hne =>
      freeIn_setP_of_not_mem ρ (fun hm => Finset.disjoint_left.mp (hdisj i hi j hj (Ne.symm hne)) hzV hm) c
    have hinv1 : ∀ j < k, j ≠ i → d ≤ (freeIn (V j) (setP ρ z c)).card ∨
        (freeIn (V j) (setP ρ z c) = ∅ ∧ ∀ x, φ j (fixP (setP ρ z c) x) = true) := by
      intro j hj hne
      rw [hfree_j j hj hne]
      rcases hinv j hj with hc | ⟨he, ht⟩
      · exact Or.inl hc
      · exact Or.inr ⟨he, fun x => by rw [← hfix1]; exact ht _⟩
    by_cases hbig : d ≤ (freeIn (V i) (setP ρ z c)).card
    · -- block `i` stays active
      refine ⟨fun x => prodP k φ (fixP (setP ρ z c) x), ⟨setP ρ z c, ?_, ?_, fun x => rfl⟩, hR1⟩
      · intro j hj
        by_cases hji : j = i
        · subst hji; exact Or.inl hbig
        · exact hinv1 j hj hji
      · have hs := sum_change hi (fun j => (freeIn (V j) (setP ρ z c)).card + 1 - d)
          (fun j => (freeIn (V j) ρ).card + 1 - d)
          (fun j hj hne => by rw [hfree_j j hj hne])
        beta_reduce at hs
        unfold mu at hmu ⊢
        omega
    · -- block `i` drops to `d - 1` free inputs: fix them to a satisfying assignment
      obtain ⟨σ, hσ⟩ := block_sat hd2 (hdep i hi) (hps i hi) ρ (Or.inl hdi) z c
      rw [hfix1] at hσ
      have hD : ∀ w ∈ freeIn (V i) (setP ρ z c), setP ρ z c w = none :=
        fun w hw => (Finset.mem_filter.mp hw).2
      have hVD : ∀ j < k, j ≠ i → ∀ w ∈ V j, w ∉ freeIn (V i) (setP ρ z c) := by
        intro j hj hne w hw hwD
        exact Finset.disjoint_left.mp (hdisj i hi j hj (Ne.symm hne)) (Finset.mem_filter.mp hwD).1 hw
      have hfree2 : ∀ j < k, j ≠ i →
          freeIn (V j) (fill (setP ρ z c) (freeIn (V i) (setP ρ z c)) σ) = freeIn (V j) ρ :=
        fun j hj hne => (freeIn_fill_of_disj _ _ _ σ (hVD j hj hne)).trans (hfree_j j hj hne)
      refine ⟨fun x => prodP k φ (fixP (fill (setP ρ z c) (freeIn (V i) (setP ρ z c)) σ) x),
        ⟨fill (setP ρ z c) (freeIn (V i) (setP ρ z c)) σ, ?_, ?_, fun x => rfl⟩, ?_⟩
      · intro j hj
        by_cases hji : j = i
        · subst hji
          refine Or.inr ⟨freeIn_fill_self _ _ σ, fun x => ?_⟩
          rw [hdep j hj _ _ (fill_agree _ _ σ x)]
          exact hσ
        · rw [freeIn_fill_of_disj _ _ _ σ (hVD j hj hji)]
          rcases hinv1 j hj hji with hc | ⟨he, ht⟩
          · exact Or.inl hc
          · exact Or.inr ⟨he, fun x => by rw [fixP_fill _ _ σ hD]; exact ht _⟩
      · have hs := sum_change hi
          (fun j => (freeIn (V j) (fill (setP ρ z c) (freeIn (V i) (setP ρ z c)) σ)).card + 1 - d)
          (fun j => (freeIn (V j) ρ).card + 1 - d)
          (fun j hj hne => by rw [hfree2 j hj hne])
        beta_reduce at hs
        rw [freeIn_fill_self] at hs
        unfold mu at hmu ⊢
        simp only [Finset.card_empty] at hs
        omega
      · have e : (fun x => prodP k φ (fixP (fill (setP ρ z c) (freeIn (V i) (setP ρ z c)) σ) x)) =
            fun x => (fun y => prodP k φ (fixP (setP ρ z c) y)) (fixS (freeIn (V i) (setP ρ z c)) σ x) := by
          funext x; rw [fixP_fill _ _ σ hD]
        rw [e]
        exact realizes_fixS σ _ (fun w hw => hVn i hi w (Finset.mem_filter.mp hw).1) hR1

/-- **Block product bound (restricted form).** -/
theorem block_product_lower_at {n k d s : ℕ} {V : ℕ → Finset ℕ} {φ : ℕ → (ℕ → Bool) → Bool}
    (hd2 : 2 ≤ d) (hVn : ∀ j < k, ∀ w ∈ V j, w < n)
    (hdisj : ∀ i < k, ∀ j < k, i ≠ j → Disjoint (V i) (V j))
    (hdep : ∀ j < k, DepOn (V j) (φ j)) (hps : ∀ j < k, PS d (V j) (φ j))
    (ρ : ℕ → Option Bool) (hinv : Inv k d V φ ρ) (hR : Realizes n (fun x => prodP k φ (fixP ρ x)) s) :
    3 * mu k d V ρ ≤ s :=
  potential_lower (BP k d V φ) (block_hstep hd2 hVn hdisj hdep hps) _ _ _
    ⟨ρ, hinv, le_rfl, fun _ => rfl⟩ hR

theorem freeIn_none (V : Finset ℕ) : freeIn V (fun _ => none) = V := by
  ext w; simp [freeIn]

theorem inv_none {k d : ℕ} {V : ℕ → Finset ℕ} {φ : ℕ → (ℕ → Bool) → Bool}
    (hcard : ∀ j < k, d ≤ (V j).card) : Inv k d V φ (fun _ => none) :=
  fun j hj => Or.inl (by rw [freeIn_none]; exact hcard j hj)

theorem mu_none (k d : ℕ) (V : ℕ → Finset ℕ) :
    mu k d V (fun _ => none) = (Finset.range k).sum fun j => (V j).card + 1 - d := by
  simp only [mu, freeIn_none]

/-- **Block product bound.** An AND of `PS d` factors (`d ≥ 2`) on disjoint blocks of at least `d` inputs
needs at least `3 · Σ_j (|V_j| + 1 - d)` gates. -/
theorem block_product_lower {n k d s : ℕ} {V : ℕ → Finset ℕ} {φ : ℕ → (ℕ → Bool) → Bool}
    (hd2 : 2 ≤ d) (hVn : ∀ j < k, ∀ w ∈ V j, w < n)
    (hdisj : ∀ i < k, ∀ j < k, i ≠ j → Disjoint (V i) (V j))
    (hdep : ∀ j < k, DepOn (V j) (φ j)) (hps : ∀ j < k, PS d (V j) (φ j))
    (hcard : ∀ j < k, d ≤ (V j).card) (hR : Realizes n (prodP k φ) s) :
    3 * (Finset.range k).sum (fun j => (V j).card + 1 - d) ≤ s := by
  rw [← mu_none]
  exact block_product_lower_at hd2 hVn hdisj hdep hps _ (inv_none hcard) hR

/-- **Restriction to a block product.** If fixing a set `F` of essential inputs of `f` leaves an AND of
`k ≥ 1` `PS d` factors on disjoint blocks of at least `d` inputs, then
`C(f) ≥ |F| + 3 · Σ_j (|V_j| + 1 - d)`. -/
theorem block_restriction_lower {n k d s : ℕ} {V : ℕ → Finset ℕ} {φ : ℕ → (ℕ → Bool) → Bool}
    {f : (ℕ → Bool) → Bool}
    (hd2 : 2 ≤ d) (hVn : ∀ j < k, ∀ w ∈ V j, w < n)
    (hdisj : ∀ i < k, ∀ j < k, i ≠ j → Disjoint (V i) (V j))
    (hdep : ∀ j < k, DepOn (V j) (φ j)) (hps : ∀ j < k, PS d (V j) (φ j))
    (hcard : ∀ j < k, d ≤ (V j).card) (hk : 0 < k)
    (F : Finset ℕ) (b : ℕ → Bool) (hFn : ∀ z ∈ F, z < n)
    (hess : ∀ z ∈ F, ∃ x, f (upd x z true) ≠ f (upd x z false))
    (hres : ∀ x, f (fixS F b x) = prodP k φ x) (h : Realizes n f s) :
    F.card + 3 * (Finset.range k).sum (fun j => (V j).card + 1 - d) ≤ s := by
  rw [← mu_none]
  have hm : 1 ≤ mu k d V (fun _ => none) := by
    rw [mu_none]
    have := Finset.single_le_sum (f := fun j => (V j).card + 1 - d) (fun j _ => Nat.zero_le _)
      (Finset.mem_range.mpr hk)
    have h0 := hcard 0 hk
    beta_reduce at this
    omega
  exact potential_restriction_lower (BP k d V φ) (block_hstep hd2 hVn hdisj hdep hps) F b hFn hess hm
    ⟨fun _ => none, inv_none hcard, le_rfl, fun x => by
      show f (fixS F b x) = prodP k φ (fixP (fun _ => none) x)
      rw [hres]; rfl⟩ h

end CircuitLemmas.GateElim
