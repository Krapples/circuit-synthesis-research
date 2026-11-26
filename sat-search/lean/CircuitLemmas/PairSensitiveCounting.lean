import CircuitLemmas.BlockProduct
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card

namespace CircuitLemmas.GateElim

noncomputable section

private abbrev Event (I : Type) := (I → Option Bool) × I × I × Bool

private def Bad {I : Type} [DecidableEq I] [Fintype I] (d : ℕ)
    (e : Event I) (g : (I → Bool) → Bool) : Prop :=
  let ⟨ρ, u, v, c⟩ := e
  u ≠ v ∧ ρ u = none ∧ ρ v = none ∧
    d ≤ (Finset.univ.filter fun i => ρ i = none).card ∧
    ∀ y : I → Bool, g (Function.update (Function.update (fun i => (ρ i).getD (y i)) u c) v true) =
      g (Function.update (Function.update (fun i => (ρ i).getD (y i)) u c) v false)

private instance {I : Type} [DecidableEq I] [Fintype I] (d : ℕ)
    (e : Event I) (g : (I → Bool) → Bool) : Decidable (Bad d e g) :=
  Classical.propDecidable _

private theorem card_bad {I : Type} [DecidableEq I] [Fintype I] (d : ℕ)
    (e : Event I) :
    Fintype.card {g : (I → Bool) → Bool // Bad d e g} ≤
      2 ^ (2 ^ Fintype.card I - 2 ^ (d - 2)) := by
  classical
  obtain ⟨ρ, u, v, c⟩ := e
  let free : Finset I := Finset.univ.filter fun i => ρ i = none
  by_cases h : u ≠ v ∧ ρ u = none ∧ ρ v = none ∧ d ≤ free.card
  · obtain ⟨huv, hu, hv, hd⟩ := h
    let S := (free.erase u).erase v
    have hu' : u ∈ free := by simp [free, hu]
    have hv' : v ∈ free.erase u := by simp [free, hv, Ne.symm huv]
    have hs : d - 2 ≤ S.card := by
      dsimp [S]
      rw [Finset.card_erase_of_mem hv', Finset.card_erase_of_mem hu']
      omega
    let row (a : S → Bool) (b : Bool) : I → Bool :=
      fun i => if h : i ∈ S then a ⟨i, h⟩
        else if i = u then c else if i = v then b else (ρ i).getD false
    have hvl (a : S → Bool) (b : Bool) : row a b v = b := by
      simp [row, S, Ne.symm huv]
    have hrow : Function.Injective (fun a => row a true) := by
      intro a b eq
      funext i
      simpa [row, i.property] using congrFun eq i.val
    have hpair (a : S → Bool) (b : Bool) :
        Function.update (Function.update (fun i => (ρ i).getD (row a false i)) u c) v b =
          row a b := by
      funext i
      by_cases hiv : i = v
      · subst i
        simp [hvl]
      by_cases hiu : i = u
      · subst i
        simp [Function.update_of_ne hiv, row, S]
      by_cases hi : i ∈ S
      · have hf : ρ i = none := by simpa [S, free, hiv, hiu] using hi
        simp [Function.update_of_ne, hiv, hiu, row, hi, hf]
      · cases hρ : ρ i <;> simp [Function.update_of_ne, hiv, hiu, row, hi, hρ]
    let removed := Finset.univ.image (fun a => row a true)
    let kept := (Finset.univ : Finset (I → Bool)) \ removed
    have hremoved : removed.card = 2 ^ S.card := by
      simp [removed, Finset.card_image_of_injective _ hrow]
    have hkept : kept.card ≤ 2 ^ Fintype.card I - 2 ^ (d - 2) := by
      dsimp [kept]
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hremoved]
      simp only [Fintype.card_fun, Fintype.card_bool]
      exact Nat.sub_le_sub_left (Nat.pow_le_pow_right (by decide) hs) _
    have hf : Function.Injective
        (fun g : {g : (I → Bool) → Bool // Bad d (ρ, u, v, c) g} =>
          fun x : kept => g.val x) := by
      intro a b eq
      apply Subtype.ext
      funext x
      by_cases hx : x ∈ removed
      · obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hx
        have hkeep : row w false ∈ kept := by
          simp only [kept, Finset.mem_sdiff, Finset.mem_univ, true_and, removed,
            Finset.mem_image, not_exists]
          intro t ht
          have he := congrFun ht v
          simp [hvl] at he
        have pair_a := a.property.2.2.2.2 (row w false)
        have pair_b := b.property.2.2.2.2 (row w false)
        rw [hpair, hpair] at pair_a pair_b
        exact pair_a.trans ((congrFun eq ⟨_, hkeep⟩).trans pair_b.symm)
      · exact congrFun eq ⟨x, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hx⟩⟩
    have hc := Fintype.card_le_of_injective _ hf
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe] at hc
    exact hc.trans (Nat.pow_le_pow_right (by decide) hkept)
  · have : IsEmpty {g : (I → Bool) → Bool // Bad d (ρ, u, v, c) g} :=
      ⟨fun g => h ⟨g.property.1, g.property.2.1, g.property.2.2.1, g.property.2.2.2.1⟩⟩
    simp

/-- A finite union bound over partial assignments, ordered pairs and fixed polarities. -/
theorem exists_pairSensitive_table {I : Type} [Fintype I] [DecidableEq I] (d : ℕ)
    (hd : d ≤ Fintype.card I)
    (hcount : 3 ^ Fintype.card I * Fintype.card I * Fintype.card I * 2 < 2 ^ (2 ^ (d - 2))) :
    ∃ g : (I → Bool) → Bool, ∀ (ρ : I → Option Bool) (u v : I) (c : Bool),
      u ≠ v → ρ u = none → ρ v = none →
      d ≤ (Finset.univ.filter fun i => ρ i = none).card →
      ∃ y : I → Bool,
        g (Function.update (Function.update (fun i => (ρ i).getD (y i)) u c) v true) ≠
        g (Function.update (Function.update (fun i => (ρ i).getD (y i)) u c) v false) := by
  classical
  have hsplit : 2 ^ (d - 2) + (2 ^ Fintype.card I - 2 ^ (d - 2)) = 2 ^ Fintype.card I := by
    have := Nat.pow_le_pow_right (by decide : 0 < 2)
      (show d - 2 ≤ Fintype.card I by omega)
    omega
  have hcount' := Nat.mul_lt_mul_of_pos_right hcount
    (show 0 < 2 ^ (2 ^ Fintype.card I - 2 ^ (d - 2)) by positivity)
  rw [← pow_add, hsplit] at hcount'
  have good : ∃ g : (I → Bool) → Bool, ∀ e : Event I, ¬ Bad d e g := by
    by_contra! hall
    let label (g : (I → Bool) → Bool) := Classical.choose (hall g)
    let inject (g : (I → Bool) → Bool) : Σ e : Event I, {g // Bad d e g} :=
      ⟨label g, ⟨g, Classical.choose_spec (hall g)⟩⟩
    have hinj : Function.Injective inject :=
      fun _ _ he => congrArg (fun p : Σ e : Event I, {g // Bad d e g} => p.2.val) he
    have hc := Fintype.card_le_of_injective inject hinj
    rw [Fintype.card_sigma] at hc
    have hb := Finset.sum_le_sum fun e (_ : e ∈ (Finset.univ : Finset (Event I))) => card_bad d e
    have he : Fintype.card (Event I) =
        3 ^ Fintype.card I * Fintype.card I * Fintype.card I * 2 := by
      simp [Nat.mul_assoc]
    rw [Finset.sum_const, Finset.card_univ, he] at hb
    simp only [Fintype.card_fun, Fintype.card_bool] at hc
    exact (not_lt_of_ge (hc.trans (by simpa using hb))) hcount'
  obtain ⟨g, hg⟩ := good
  refine ⟨g, fun ρ u v c huv hu hv hd => ?_⟩
  by_contra! hn
  exact hg (ρ, u, v, c) ⟨huv, hu, hv, hd, hn⟩

/-- The finite counting criterion yields the predicate consumed by `block_restriction_lower`. -/
theorem exists_PS (V : Finset ℕ) (d : ℕ) (hd : d ≤ V.card)
    (hcount : 3 ^ V.card * V.card * V.card * 2 < 2 ^ (2 ^ (d - 2))) :
    ∃ φ, DepOn V φ ∧ PS d V φ := by
  classical
  obtain ⟨g, hg⟩ := exists_pairSensitive_table (I := V) d
    (by simpa using hd) (by simpa using hcount)
  refine ⟨fun x => g (fun i : V => x i), ?_, ?_⟩
  · intro x y h
    exact congrArg g (funext fun i => h i i.property)
  · intro ρ hfree u hu v hv huv c
    have hu' := mem_freeIn.mp hu
    have hv' := mem_freeIn.mp hv
    let u' : V := ⟨u, hu'.1⟩
    let v' : V := ⟨v, hv'.1⟩
    let ρ' (i : V) := ρ i
    have hmap : (Finset.univ.filter fun i : V => ρ' i = none).map
        (⟨Subtype.val, Subtype.val_injective⟩ : V ↪ ℕ) = freeIn V ρ := by
      ext i
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, mem_freeIn]
      constructor
      · rintro ⟨j, hj, rfl⟩
        exact ⟨j.property, hj⟩
      · rintro ⟨hi, hρ⟩
        exact ⟨⟨i, hi⟩, hρ, rfl⟩
    have hfree' : d ≤ (Finset.univ.filter fun i : V => ρ' i = none).card := by
      simpa only [Finset.card_map, ← hmap] using hfree
    obtain ⟨y, hy⟩ := hg ρ' u' v' c (fun h => huv (congrArg Subtype.val h))
      hu'.2 hv'.2 hfree'
    let x (i : ℕ) := if h : i ∈ V then y ⟨i, h⟩ else false
    have hx (b : Bool) :
        (fun i : V => fixP ρ (upd (upd x v b) u c) i) =
          Function.update (Function.update (fun i : V => (ρ' i).getD (y i)) u' c) v' b := by
      funext i
      by_cases hiu : i = u'
      · subst i
        have hne : u' ≠ v' := fun h => huv (congrArg Subtype.val h)
        simp [fixP, upd, u', hu'.2, Function.update_of_ne hne]
      by_cases hiv : i = v'
      · subst i
        simp [fixP, upd, v', hv'.2, Ne.symm huv]
      have hnu : (i : ℕ) ≠ u := fun h => hiu (Subtype.ext h)
      have hnv : (i : ℕ) ≠ v := fun h => hiv (Subtype.ext h)
      simp [fixP, upd, Function.update_of_ne, hiu, hiv, hnu, hnv, x, ρ', i.property]
    refine ⟨x, ?_⟩
    change g (fun i : V => fixP ρ (upd (upd x v true) u c) i) ≠
      g (fun i : V => fixP ρ (upd (upd x v false) u c) i)
    rwa [hx, hx]

/-- A convenient numerical premise that avoids computing the number of complete truth tables. -/
theorem pairSensitive_count_of_four_mul_lt {r d : ℕ} (hV : 0 < r) (hpow : 4 * r < 2 ^ (d - 2)) :
    3 ^ r * r * r * 2 < 2 ^ (2 ^ (d - 2)) := by
  have hr : r ≤ 2 ^ r := Nat.lt_two_pow_self.le
  have hthree : 3 ^ r < 4 ^ r := Nat.pow_lt_pow_left (by decide) (by omega)
  calc
    3 ^ r * r * r * 2 = 3 ^ r * (r * r * 2) := by ring
    _ < 4 ^ r * (r * r * 2) := Nat.mul_lt_mul_of_pos_right hthree (by positivity)
    _ ≤ 4 ^ r * (2 ^ r * 2 ^ r * 2) := by gcongr
    _ = 2 ^ (4 * r + 1) := by
      have he : 4 ^ r = 2 ^ r * 2 ^ r := by rw [← mul_pow]; rfl
      rw [he, show 4 * r + 1 = (r + r) + (r + r) + 1 by omega]
      simp only [pow_add, pow_one]
      ring
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)

/-- The logarithmic threshold meets the finite counting condition for every width at least eight. -/
theorem pairSensitive_logarithmic_parameters {r : ℕ} (hr : 8 ≤ r) :
    let d := Nat.log2 r + 5
    2 ≤ d ∧ d ≤ r ∧ 3 ^ r * r * r * 2 < 2 ^ (2 ^ (d - 2)) := by
  have hpos : 0 < r := by omega
  have haux (t : ℕ) : 8 + t < 2 ^ (t + 4) := by
    induction t with
    | zero => decide
    | succ t ih =>
      rw [show t + 1 + 4 = t + 4 + 1 by omega, pow_succ]
      omega
  have hwidth : Nat.log2 r + 5 ≤ r := by
    have h := haux (r - 8)
    rw [show 8 + (r - 8) = r by omega, show r - 8 + 4 = r - 4 by omega] at h
    have := (Nat.log2_lt hpos.ne').mpr h
    omega
  refine ⟨by omega, hwidth, pairSensitive_count_of_four_mul_lt hpos ?_⟩
  rw [show Nat.log2 r + 5 - 2 = (Nat.log2 r + 1) + 2 by omega, pow_add]
  have h := Nat.lt_log2_self (n := r)
  norm_num at *
  omega

/-- Pair-sensitive tables exist with a logarithmic threshold for every width at least eight. -/
theorem exists_PS_logarithmic (V : Finset ℕ) (hV : 8 ≤ V.card) :
    ∃ φ, DepOn V φ ∧ PS (Nat.log2 V.card + 5) V φ :=
  let ⟨_, hd, hcount⟩ := pairSensitive_logarithmic_parameters hV
  exists_PS V _ hd hcount

/-- Copy a pair-sensitive factor onto a renamed block, preserving its restriction property. -/
theorem pairSensitive_reindex {d : ℕ} {V : Finset ℕ} {φ : (ℕ → Bool) → Bool}
    (hdep : DepOn V φ) (hps : PS d V φ) (e : ℕ ↪ ℕ) :
    DepOn (V.map e) (fun x => φ (x ∘ e)) ∧ PS d (V.map e) (fun x => φ (x ∘ e)) := by
  classical
  constructor
  · intro x y h
    exact hdep _ _ (fun i hi => h (e i) (Finset.mem_map.mpr ⟨i, hi, rfl⟩))
  · intro ρ hfree u hu v hv huv c
    have he : (freeIn V (ρ ∘ e)).map e = freeIn (V.map e) ρ := by
      ext i
      simp only [Finset.mem_map, mem_freeIn, Function.comp_apply]
      constructor
      · rintro ⟨j, ⟨hj, hρ⟩, rfl⟩
        exact ⟨⟨j, hj, rfl⟩, hρ⟩
      · rintro ⟨⟨j, hj, rfl⟩, hρ⟩
        exact ⟨j, ⟨hj, hρ⟩, rfl⟩
    rw [← he, Finset.card_map] at hfree
    change u ∈ freeIn (V.map e) ρ at hu
    change v ∈ freeIn (V.map e) ρ at hv
    rw [← he] at hu hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hu
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hv
    obtain ⟨z, hz⟩ := hps (ρ ∘ e) hfree i hi j hj (fun h => huv (congrArg e h)) c
    let x := z ∘ Function.invFun e
    have hread (b : Bool) :
        (fixP ρ (upd (upd x (e j) b) (e i) c)) ∘ e =
          fixP (ρ ∘ e) (upd (upd z j b) i c) := by
      funext w
      simp [fixP, upd, e.injective.eq_iff, x, Function.leftInverse_invFun e.injective w]
    refine ⟨x, ?_⟩
    change φ (fixP ρ (upd (upd x (e j) true) (e i) c) ∘ e) ≠
      φ (fixP ρ (upd (upd x (e j) false) (e i) c) ∘ e)
    rwa [hread, hread]

end

end CircuitLemmas.GateElim
