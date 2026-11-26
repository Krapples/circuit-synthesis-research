import Mathlib

namespace CoverUnion4653

variable {α : Type*} [DecidableEq α]

def step (F : Set (Set α)) (r : Set α × Set α) : Set (Set α) :=
  {S | S ∈ F ∨ (r.1 ∈ F ∧ r.2 ∈ F ∧ S ⊆ r.1 ∪ r.2)}

def Consistent (P : Finset α) (F : Set (Set α)) (f : α → α) : Prop :=
  ∀ S ∈ F, ∀ a ∈ P, ∀ b ∈ P, a ∈ S → b ∈ S → f a = f b

def meet : Option (Finset α) → Option (Finset α) → Option (Finset α)
  | some A, some B => some (A ∪ B)
  | _, _ => none

def holds (x : α → Prop) : Option (Finset α) → Prop
  | none => False
  | some A => ∀ a ∈ A, x a

theorem holds_meet (x : α → Prop) (D E : Option (Finset α)) :
    holds x (meet D E) ↔ holds x D ∧ holds x E := by
  cases D <;> cases E <;> simp [holds, meet]
  exact ⟨fun h => ⟨fun a ha => h a (Or.inl ha), fun a ha => h a (Or.inr ha)⟩,
    fun ⟨h, k⟩ a ha => ha.elim (h a) (k a)⟩

theorem relabel_bound (P : Finset α) (f : α → α) (u v : α)
    (g : α → α) (hg : ∀ x, g x = if f x = v then u else f x) :
    (P.image f).card ≤ (P.image g).card + 1 := by
  have contain : P.image f ⊆ insert v (P.image g) := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    by_cases eq : f x = v
    · exact Finset.mem_insert.mpr (Or.inl eq)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr ⟨x, hx, by simp [hg, eq]⟩))
  exact (Finset.card_le_card contain).trans (Finset.card_insert_le v (P.image g))

theorem step_labels (P : Finset α) (F : Set (Set α)) (r : Set α × Set α)
    (f : α → α) (hf : Consistent P F f) :
    ∃ g : α → α, Consistent P (step F r) g ∧ (P.image f).card ≤ (P.image g).card + 1 := by
  classical
  by_cases active : r.1 ∈ F ∧ r.2 ∈ F
  · by_cases a : ∃ x ∈ P, x ∈ r.1
    · by_cases b : ∃ x ∈ P, x ∈ r.2
      · obtain ⟨a, ha, ha'⟩ := a
        obtain ⟨b, hb, hb'⟩ := b
        let g (x : α) := if f x = f b then f a else f x
        refine ⟨g, ?_, relabel_bound P f (f a) (f b) g (fun _ => rfl)⟩
        intro S hS x hx y hy hx' hy'
        rcases hS with old | ⟨_, _, add⟩
        · exact congrArg (fun z => if z = f b then f a else z) (hf S old x hx y hy hx' hy')
        · have merge (z : α) (hz : z ∈ P) (hz' : z ∈ S) : g z = f a := by
            rcases add hz' with left | right
            · simp [g, hf r.1 active.1 z hz a ha left ha']
            · simp [g, hf r.2 active.2 z hz b hb right hb']
          exact (merge x hx hx').trans (merge y hy hy').symm
      · refine ⟨f, ?_, by omega⟩
        intro S hS x hx y hy hx' hy'
        rcases hS with old | ⟨_, _, add⟩
        · exact hf S old x hx y hy hx' hy'
        · have inside (z : α) (hz : z ∈ P) (hz' : z ∈ S) : z ∈ r.1 :=
            (add hz').resolve_right (fun no => b ⟨z, hz, no⟩)
          exact hf r.1 active.1 x hx y hy (inside x hx hx') (inside y hy hy')
    · refine ⟨f, ?_, by omega⟩
      intro S hS x hx y hy hx' hy'
      rcases hS with old | ⟨_, _, add⟩
      · exact hf S old x hx y hy hx' hy'
      · have inside (z : α) (hz : z ∈ P) (hz' : z ∈ S) : z ∈ r.2 :=
          (add hz').resolve_left (fun no => a ⟨z, hz, no⟩)
        exact hf r.2 active.2 x hx y hy (inside x hx hx') (inside y hy hy')
  · exact ⟨f, (fun S hS => hf S (hS.resolve_right fun h => active ⟨h.1, h.2.1⟩)), by omega⟩

theorem fold_labels (P : Finset α) (F : Set (Set α)) (R : List (Set α × Set α))
    (f : α → α) (hf : Consistent P F f) :
    ∃ g : α → α, Consistent P (R.foldl step F) g ∧ (P.image f).card ≤ (P.image g).card + R.length := by
  induction R generalizing F f with
  | nil => exact ⟨f, hf, by simp⟩
  | cons r R ih =>
    obtain ⟨f', hf', bound⟩ := step_labels P F r f hf
    obtain ⟨g, hg, rest⟩ := ih (step F r) f' hf'
    exact ⟨g, hg, by simp only [List.length_cons]; omega⟩

theorem private_edge_lower_bound (P : Finset α) (F : Set (Set α)) (R : List (Set α × Set α))
    (initial : Consistent P F id) (S : Set α) (covered : (P : Set α) ⊆ S)
    (hs : S ∈ R.foldl step F) : P.card ≤ R.length + 1 := by
  obtain ⟨g, hg, bound⟩ := fold_labels P F R id initial
  have final : (P.image g).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
    exact hg S hs x hx y hy (covered hx) (covered hy)
  rw [Finset.image_id] at bound
  omega

theorem output_cover_lower_bound (P : Finset α) (F : Set (Set α)) (R : List (Set α × Set α))
    (initial : Consistent P F id) (outputs : Finset (Finset α))
    (available : ∀ S ∈ outputs, (S : Set α) ∈ R.foldl step F)
    (cover : ∀ a ∈ P, ∃ S ∈ outputs, a ∈ S) : P.card ≤ R.length + outputs.card := by
  classical
  obtain ⟨g, hg, bound⟩ := fold_labels P F R id initial
  let labels (S : Finset α) := (P.filter fun a => a ∈ S).image g
  have small (S : Finset α) (hS : S ∈ outputs) : (labels S).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨hx, hx'⟩ := Finset.mem_filter.mp hx
    obtain ⟨hy, hy'⟩ := Finset.mem_filter.mp hy
    exact hg S (available S hS) x hx y hy hx' hy'
  have contain : P.image g ⊆ outputs.biUnion labels := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨S, hS, hx'⟩ := cover x hx
    exact Finset.mem_biUnion.mpr ⟨S, hS, Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hx'⟩, rfl⟩⟩
  have final : (P.image g).card ≤ outputs.card := calc
    _ ≤ (outputs.biUnion labels).card := Finset.card_le_card contain
    _ ≤ ∑ S ∈ outputs, (labels S).card := Finset.card_biUnion_le
    _ ≤ ∑ S ∈ outputs, 1 := Finset.sum_le_sum small
    _ = outputs.card := by simp
  rw [Finset.image_id] at bound
  omega

omit [DecidableEq α] in
theorem availability_complement_step (F : Set (Set α)) (r : Set α × Set α) (S : Set α) :
    S ∉ step F r ↔ S ∉ F ∧ (S ⊆ r.1 ∪ r.2 → r.1 ∉ F ∨ r.2 ∉ F) := by
  classical
  change ¬ (S ∈ F ∨ _) ↔ _
  tauto

omit [DecidableEq α] in
theorem first_idle (P : Finset α) (F : Set (Set α)) (r : Set α × Set α)
    (initial : Consistent P F id) (inactive : r.1 ∉ F ∨ ∀ x ∈ P, x ∉ r.1) :
    Consistent P (step F r) id := by
  intro S hS x hx y hy hx' hy'
  rcases hS with old | ⟨ha, hb, add⟩
  · exact initial S old x hx y hy hx' hy'
  · rcases inactive with no | avoid
    · exact (no ha).elim
    · exact initial r.2 hb x hx y hy
        ((add hx').resolve_left (avoid x hx)) ((add hy').resolve_left (avoid y hy))

omit [DecidableEq α] in
theorem restrict_start (R : List (Set α × Set α)) (F G : Set (Set α)) (T : Set α)
    (matchTarget : T ∈ F ↔ T ∈ G)
    (matchOperands : ∀ r ∈ R, (r.1 ∈ F ↔ r.1 ∈ G) ∧ (r.2 ∈ F ↔ r.2 ∈ G)) :
    T ∈ R.foldl step F ↔ T ∈ R.foldl step G := by
  induction R generalizing F G with
  | nil => exact matchTarget
  | cons r R ih =>
    obtain ⟨a, b⟩ := matchOperands r (by simp)
    have update (S : Set α) (same : S ∈ F ↔ S ∈ G) : S ∈ step F r ↔ S ∈ step G r := by
      change (_ ∨ _) ↔ (_ ∨ _)
      rw [same, a, b]
    exact ih (step F r) (step G r) (update T matchTarget) (fun s hs => by
      obtain ⟨h₁, h₂⟩ := matchOperands s (by simp [hs])
      exact ⟨update s.1 h₁, update s.2 h₂⟩)

abbrev Vertex := Fin 42
abbrev Edge := Vertex × Vertex

def incidence (e : Edge) : Prop :=
  e.1.val < 21 ∧ 21 ≤ e.2.val ∧ (e.2.val + 21 - e.1.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)

instance (e : Edge) : Decidable (incidence e) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def selected (v : Vertex) : Prop := v ∉ ([0, 2, 7, 8, 31, 32, 37, 39] : List Vertex)

instance (v : Vertex) : Decidable (selected v) := inferInstanceAs (Decidable (¬ _))

def privateEdges : Finset Edge :=
  ([(1, 39), (3, 31), (4, 32), (5, 31), (6, 32), (9, 37), (10, 31), (11, 31),
    (12, 32), (13, 39), (14, 31), (15, 32), (16, 37), (17, 37), (18, 39),
    (19, 39), (20, 37), (0, 21), (2, 22), (2, 23), (7, 24), (8, 25), (0, 26),
    (7, 27), (0, 28), (8, 29), (2, 30), (7, 33), (8, 34), (7, 35), (8, 36),
    (0, 38), (2, 40), (0, 41)] : List Edge).toFinset

def start (Z : Set Vertex) : Set (Set Edge) :=
  {S | S = ∅ ∨ ∃ v ∈ Z, ∀ e ∈ S, e.1 = v ∨ e.2 = v}

theorem selected_cover : ∀ e : Edge, incidence e → selected e.1 ∨ selected e.2 := by decide +kernel

theorem private_per_center : ∀ v : Vertex, selected v →
    (privateEdges.filter fun e => e.1 = v ∨ e.2 = v).card ≤ 1 := by decide +kernel

theorem private_incident : ∀ e ∈ privateEdges, incidence e := by decide +kernel

theorem private_size : privateEdges.card = 34 := by decide +kernel

theorem private_not_both : ∀ e ∈ privateEdges, ¬ (selected e.1 ∧ selected e.2) := by decide +kernel

theorem rectangle_equality_shape (s t : Fin 22)
    (bound : 25 * s.val ≤ (21 - t.val) * (s.val + 4))
    (tight : s.val * t.val = 36) : s.val = 6 ∧ t.val = 6 := by
  exact (by decide +kernel : ∀ a b : Fin 22,
    25 * a.val ≤ (21 - b.val) * (a.val + 4) →
    a.val * b.val = 36 → a.val = 6 ∧ b.val = 6) s t bound tight

theorem rectangle_residual_counts (s : Finset Vertex) (d : Vertex → ℤ)
    (card : s.card = 15) (sum : ∑ v ∈ s, d v = 30) (squares : ∑ v ∈ s, (d v)^2 = 60) :
    ∀ v ∈ s, d v = 2 := by
  have term (v : Vertex) : (d v - 2)^2 = d v ^ 2 - 4 * d v + 4 := by ring
  have zero : ∑ v ∈ s, (d v - 2)^2 = 0 := by
    simp [term, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, squares, sum, card]
  intro v hv
  have small := Finset.single_le_sum (f := fun v => (d v - 2)^2)
    (fun v _ => sq_nonneg (d v - 2)) hv
  rw [zero] at small
  nlinarith [sq_nonneg (d v - 2)]

theorem pg4_union_lower_bound (R : List (Set Edge × Set Edge))
    (hR : ∀ Z : Set Vertex,
      (∀ e : Edge, incidence e → e.1 ∈ Z ∨ e.2 ∈ Z) →
      {e | incidence e} ∈ R.foldl step (start Z)) : 33 ≤ R.length := by
  have init : Consistent privateEdges (start {v | selected v}) id := by
    intro S hS a ha b hb ha' hb'
    rcases hS with empty | ⟨v, hv, hv'⟩
    · exact (empty ▸ ha').elim
    · exact Finset.card_le_one.mp (private_per_center v hv) a
        (Finset.mem_filter.mpr ⟨ha, hv' a ha'⟩) b (Finset.mem_filter.mpr ⟨hb, hv' b hb'⟩)
  have lower := private_edge_lower_bound privateEdges _ R init {e | incidence e}
    private_incident (hR {v | selected v} selected_cover)
  rw [private_size] at lower
  omega

def cyclicShift (k : Fin 21) : Equiv.Perm Vertex :=
  finSumFinEquiv.symm.trans (((Equiv.addRight k).sumCongr (Equiv.addRight k)).trans finSumFinEquiv)

def edgeShift (k : Fin 21) : Equiv.Perm Edge :=
  (cyclicShift k).prodCongr (cyclicShift k)

theorem shift_incidence (k : Fin 21) (e : Edge) : incidence (edgeShift k e) ↔ incidence e := by
  exact (by decide +kernel : ∀ t : Fin 21, ∀ a b : Vertex,
    incidence (edgeShift t (a, b)) ↔ incidence (a, b)) k e.1 e.2

theorem shift_can_omit (v : Vertex) : ∃ k : Fin 21, ¬ selected (cyclicShift k v) :=
  (by decide +kernel : ∀ a : Vertex, ∃ k : Fin 21, ¬ selected (cyclicShift k a)) v

theorem shift_can_keep (e : Edge) : ∃ k : Fin 21,
    selected (cyclicShift k e.1) ∧ selected (cyclicShift k e.2) :=
  (by decide +kernel : ∀ a b : Vertex, ∃ k : Fin 21,
    selected (cyclicShift k a) ∧ selected (cyclicShift k b)) e.1 e.2

theorem unique_common_center {x y : Edge} (hx : incidence x) (hy : incidence y) (neq : x ≠ y)
    {a b : Vertex} (xa : x.1 = a ∨ x.2 = a) (ya : y.1 = a ∨ y.2 = a)
    (xb : x.1 = b ∨ x.2 = b) (yb : y.1 = b ∨ y.2 = b) : a = b := by
  have leftRight (u : Vertex) : u = x.1 → u = y.2 → False := by
    intro hu hv
    have h := congrArg Fin.val (hu.symm.trans hv)
    have := hx.1
    have := hy.2.1
    omega
  have rightLeft (u : Vertex) : u = x.2 → u = y.1 → False := by
    intro hu hv
    have h := congrArg Fin.val (hu.symm.trans hv)
    have := hx.2.1
    have := hy.1
    omega
  have same (u : Vertex) (h₁ : x.1 = u ∨ x.2 = u) (h₂ : y.1 = u ∨ y.2 = u) :
      (x.1 = u ∧ y.1 = u) ∨ (x.2 = u ∧ y.2 = u) := by
    rcases h₁ with g | g <;> rcases h₂ with h | h
    · exact Or.inl ⟨g, h⟩
    · exact (leftRight u g.symm h.symm).elim
    · exact (rightLeft u g.symm h.symm).elim
    · exact Or.inr ⟨g, h⟩
  rcases same a xa ya with ⟨ha, ha'⟩ | ⟨ha, ha'⟩ <;>
    rcases same b xb yb with ⟨hb, hb'⟩ | ⟨hb, hb'⟩
  · exact ha.symm.trans hb
  · exact (neq (Prod.ext (ha.trans ha'.symm) (hb.trans hb'.symm))).elim
  · exact (neq (Prod.ext (hb.trans hb'.symm) (ha.trans ha'.symm))).elim
  · exact ha.symm.trans hb

def shiftedCover (k : Fin 21) : Set Vertex := {v | selected (cyclicShift k v)}

def shiftedPrivate (k : Fin 21) : Finset Edge := privateEdges.map (edgeShift k).symm.toEmbedding

theorem mem_shifted_private (k : Fin 21) (e : Edge) :
    e ∈ shiftedPrivate k ↔ edgeShift k e ∈ privateEdges := by
  simp [shiftedPrivate]

theorem shifted_private_incidence (k : Fin 21) {e : Edge} (he : e ∈ shiftedPrivate k) : incidence e := by
  exact (shift_incidence k e).mp (private_incident _ ((mem_shifted_private k e).mp he))

theorem shifted_private_not_both (k : Fin 21) {e : Edge} (he : e ∈ shiftedPrivate k) :
    ¬ (e.1 ∈ shiftedCover k ∧ e.2 ∈ shiftedCover k) := by
  exact private_not_both _ ((mem_shifted_private k e).mp he)

theorem shifted_cover_valid (k : Fin 21) (e : Edge) (he : incidence e) :
    e.1 ∈ shiftedCover k ∨ e.2 ∈ shiftedCover k := by
  exact selected_cover (edgeShift k e) ((shift_incidence k e).mpr he)

theorem shifted_initial (k : Fin 21) : Consistent (shiftedPrivate k) (start (shiftedCover k)) id := by
  intro S hS a ha b hb ha' hb'
  rcases hS with empty | ⟨v, hv, hv'⟩
  · exact (empty ▸ ha').elim
  have both (e : Edge) (he : e ∈ shiftedPrivate k) (he' : e ∈ S) :
      edgeShift k e ∈ privateEdges.filter (fun p => p.1 = cyclicShift k v ∨ p.2 = cyclicShift k v) := by
    refine Finset.mem_filter.mpr ⟨(mem_shifted_private k e).mp he, ?_⟩
    exact (hv' e he').imp (congrArg (cyclicShift k)) (congrArg (cyclicShift k))
  exact (edgeShift k).injective
    (Finset.card_le_one.mp (private_per_center _ hv) _ (both a ha ha') _ (both b hb hb'))

theorem operand_idle_for_some_shift (A : Set Edge) : ∃ k : Fin 21,
    A ∉ start (shiftedCover k) ∨ ∀ e ∈ shiftedPrivate k, e ∉ A := by
  classical
  by_cases two : ∃ e ∈ A, ∃ f ∈ A, incidence e ∧ incidence f ∧ e ≠ f
  · obtain ⟨e, he, f, hf, eInc, fInc, distinct⟩ := two
    by_cases centered : ∃ v : Vertex, ∀ j ∈ A, j.1 = v ∨ j.2 = v
    · obtain ⟨v, hv⟩ := centered
      obtain ⟨k, excluded⟩ := shift_can_omit v
      refine ⟨k, Or.inl ?_⟩
      intro available
      rcases available with empty | ⟨u, hu, isCenter⟩
      · exact (empty ▸ he).elim
      · have same := unique_common_center eInc fInc distinct (isCenter e he) (isCenter f hf) (hv e he) (hv f hf)
        exact excluded (same ▸ hu)
    · refine ⟨0, Or.inl ?_⟩
      intro available
      rcases available with empty | ⟨u, _, hu⟩
      · exact (empty ▸ he).elim
      · exact centered ⟨u, hu⟩
  · by_cases single : ∃ e ∈ A, incidence e
    · obtain ⟨e, he, eInc⟩ := single
      obtain ⟨k, he₁, he₂⟩ := shift_can_keep e
      refine ⟨k, Or.inr ?_⟩
      intro f hf hf'
      have same : e = f := by
        by_contra h
        exact two ⟨e, he, f, hf', eInc, shifted_private_incidence k hf, h⟩
      exact shifted_private_not_both k hf (same ▸ ⟨he₁, he₂⟩)
    · exact ⟨0, Or.inr (fun e he ha => single ⟨e, ha, shifted_private_incidence 0 he⟩)⟩

theorem pg4_union_lower_bound_34 (R : List (Set Edge × Set Edge))
    (hR : ∀ Z : Set Vertex,
      (∀ e : Edge, incidence e → e.1 ∈ Z ∨ e.2 ∈ Z) →
      {e | incidence e} ∈ R.foldl step (start Z)) : 34 ≤ R.length := by
  cases R with
  | nil => have impossible := pg4_union_lower_bound [] hR; simp at impossible
  | cons r R =>
    obtain ⟨k, idle⟩ := operand_idle_for_some_shift r.1
    have full := hR (shiftedCover k) (shifted_cover_valid k)
    have cost := private_edge_lower_bound (shiftedPrivate k) (step (start (shiftedCover k)) r)
      R (first_idle _ _ _ (shifted_initial k) idle) {e | incidence e}
      (fun _ hx => shifted_private_incidence k hx) full
    simpa [shiftedPrivate, private_size, Nat.add_comm] using cost

def allEdges : Finset Edge := Finset.univ.filter incidence

def operandCenters (R : List (Set Edge × Set Edge)) : Set Vertex :=
  {v | ∃ r ∈ R, ∃ A : Set Edge, (A = r.1 ∨ A = r.2) ∧
    (∃ e ∈ A, ∃ f ∈ A, incidence e ∧ incidence f ∧ e ≠ f) ∧
    ∀ e ∈ A, e.1 = v ∨ e.2 = v}

theorem not_all_initial (Z : Set Vertex) : {e | incidence e} ∉ start Z := by
  intro h
  have e : ((0, 21) : Edge) ∈ {e | incidence e} := by decide +kernel
  have f : ((1, 22) : Edge) ∈ {e | incidence e} := by decide +kernel
  rcases h with empty | ⟨v, _, center⟩
  · exact (empty ▸ e).elim
  · rcases center (0, 21) e with h | h <;> rcases center (1, 22) f with k | k
    all_goals exact (by decide +kernel : (0 : Vertex) ≠ 1 ∧ (0 : Vertex) ≠ 22 ∧
      (21 : Vertex) ≠ 1 ∧ (21 : Vertex) ≠ 22).elim (fun h₁ h₂ => by
        first | exact h₁ (h.trans k.symm) | exact h₂.1 (h.trans k.symm) |
          exact h₂.2.1 (h.trans k.symm) | exact h₂.2.2 (h.trans k.symm))

theorem independent_operand_centers_lower_bound (R : List (Set Edge × Set Edge))
    (independent : ∀ e : Edge, incidence e → ¬ (e.1 ∈ operandCenters R ∧ e.2 ∈ operandCenters R))
    (hR : ∀ Z : Set Vertex,
      (∀ e : Edge, incidence e → e.1 ∈ Z ∨ e.2 ∈ Z) →
      {e | incidence e} ∈ R.foldl step (start Z)) : 104 ≤ R.length := by
  classical
  let Z : Set Vertex := (operandCenters R)ᶜ
  let T : Set Edge := {e | incidence e}
  let thin (A : Set Edge) := ∀ e ∈ A, ∀ f ∈ A, incidence e → incidence f → e = f
  let F : Set (Set Edge) := {A | A ∈ start Z ∧ thin A}
  have cover (e : Edge) (he : incidence e) : e.1 ∈ Z ∨ e.2 ∈ Z := not_and_or.mp (independent e he)
  have transfer : ∀ r ∈ R, (r.1 ∈ start Z ↔ r.1 ∈ F) ∧ (r.2 ∈ start Z ↔ r.2 ∈ F) := by
    intro r hr
    have test (A : Set Edge) (hA : A = r.1 ∨ A = r.2) : A ∈ start Z ↔ A ∈ F := by
      constructor
      · intro ha
        refine ⟨ha, ?_⟩
        intro e he f hf eInc fInc
        by_contra distinct
        rcases ha with empty | ⟨v, hv, centered⟩
        · exact (empty ▸ he).elim
        · exact hv ⟨r, hr, A, hA, ⟨e, he, f, hf, eInc, fInc, distinct⟩, centered⟩
      · exact fun h => h.1
    exact ⟨test r.1 (Or.inl rfl), test r.2 (Or.inr rfl)⟩
  have final : T ∈ R.foldl step F :=
    (restrict_start R (start Z) F T ⟨fun h => (not_all_initial Z h).elim, fun h => h.1⟩ transfer).mp (hR Z cover)
  have init : Consistent allEdges F id := fun A hA e he f hf he' hf' =>
    hA.2 e he' f hf' (Finset.mem_filter.mp he).2 (Finset.mem_filter.mp hf).2
  have count := private_edge_lower_bound allEdges F R init T (fun _ he => (Finset.mem_filter.mp he).2) final
  have concrete : allEdges.card = 105 := by decide +kernel
  omega

omit [DecidableEq α] in
theorem project_fold (R : List (Set α × Set α)) (F G : Set (Set α)) (T K : Set α)
    (target : T ∈ F → T ∩ K ∈ G)
    (operands : ∀ r ∈ R, (r.1 ∈ F → r.1 ∩ K ∈ G) ∧ (r.2 ∈ F → r.2 ∩ K ∈ G))
    (available : T ∈ R.foldl step F) :
    T ∩ K ∈ (R.map (fun r => (r.1 ∩ K, r.2 ∩ K))).foldl step G := by
  induction R generalizing F G with
  | nil => exact target available
  | cons r R ih =>
    obtain ⟨left, right⟩ := operands r (by simp)
    have advance (S : Set α) (lift : S ∈ F → S ∩ K ∈ G) (h : S ∈ step F r) :
        S ∩ K ∈ step G (r.1 ∩ K, r.2 ∩ K) := by
      rcases h with initial | ⟨a, b, small⟩
      · exact Or.inl (lift initial)
      · refine Or.inr ⟨left a, right b, ?_⟩
        intro e he
        rcases small he.1 with ha | hb
        · exact Or.inl ⟨ha, he.2⟩
        · exact Or.inr ⟨hb, he.2⟩
    exact ih _ _ (advance T target) (fun s hs => by
      obtain ⟨a, b⟩ := operands s (by simp [hs])
      exact ⟨advance s.1 a, advance s.2 b⟩) available

abbrev SplitVertex := Vertex ⊕ (Edge × Vertex)

noncomputable def splitEndpoint (R : List (Set Edge × Set Edge)) (e : Edge) (v : Vertex) :
    SplitVertex := by
  classical exact if v ∈ operandCenters R then .inl v else .inr (e, v)

theorem splitEndpoint_fresh (R : List (Set Edge × Set Edge)) (e f : Edge) (v w : Vertex)
    (fresh : v ∉ operandCenters R) (same : splitEndpoint R e v = splitEndpoint R f w) : e = f := by
  classical
  by_cases marked : w ∈ operandCenters R
  · simp [splitEndpoint, fresh, marked] at same
  · have pair : (e, v) = (f, w) := Sum.inr.inj (by simpa only [splitEndpoint, if_neg fresh, if_neg marked] using same)
    exact congrArg Prod.fst pair

def splitStart (R : List (Set Edge × Set Edge)) (W : Set SplitVertex) : Set (Set Edge) :=
  {S | S = ∅ ∨ ∃ w ∈ W, ∀ e ∈ S, splitEndpoint R e e.1 = w ∨ splitEndpoint R e e.2 = w}

theorem split_cover_transport (R : List (Set Edge × Set Edge))
    (hR : ∀ Z : Set Vertex,
      (∀ e : Edge, incidence e → e.1 ∈ Z ∨ e.2 ∈ Z) →
      {e | incidence e} ∈ R.foldl step (start Z))
    (W : Set SplitVertex)
    (cover : ∀ e : Edge, incidence e → splitEndpoint R e e.1 ∈ W ∨ splitEndpoint R e e.2 ∈ W) :
    {e | incidence e} ∈ (R.map (fun r => (r.1 ∩ {e | incidence e}, r.2 ∩ {e | incidence e}))).foldl
      step (splitStart R W) := by
  classical
  let T : Set Edge := {e | incidence e}
  let Z : Set Vertex := {v | v ∉ operandCenters R ∨ Sum.inl v ∈ W}
  have origCover (e : Edge) (he : incidence e) : e.1 ∈ Z ∨ e.2 ∈ Z := by
    by_cases a : e.1 ∈ operandCenters R
    · by_cases b : e.2 ∈ operandCenters R
      · rcases cover e he with h | h
        · exact Or.inl (Or.inr (by simpa [splitEndpoint, a] using h))
        · exact Or.inr (Or.inr (by simpa [splitEndpoint, b] using h))
      · exact Or.inr (Or.inl b)
    · exact Or.inl (Or.inl a)
  have liftOperand (r : Set Edge × Set Edge) (hr : r ∈ R) (S : Set Edge)
      (side : S = r.1 ∨ S = r.2) (h : S ∈ start Z) : S ∩ T ∈ splitStart R W := by
    by_cases empty : S ∩ T = ∅
    · exact Or.inl empty
    obtain ⟨e, he⟩ := Set.nonempty_iff_ne_empty.mpr empty
    by_cases thin : ∀ f ∈ S ∩ T, f = e
    · rcases cover e he.2 with h₁ | h₂
      · exact Or.inr ⟨splitEndpoint R e e.1, h₁, fun f hf => Or.inl (by rw [thin f hf])⟩
      · exact Or.inr ⟨splitEndpoint R e e.2, h₂, fun f hf => Or.inr (by rw [thin f hf])⟩
    push Not at thin
    obtain ⟨f, hf, distinct⟩ := thin
    rcases h with no | ⟨v, hv, centered⟩
    · exact (no ▸ he.1).elim
    have marked : v ∈ operandCenters R :=
      ⟨r, hr, S, side, ⟨f, hf.1, e, he.1, hf.2, he.2, distinct⟩, centered⟩
    refine Or.inr ⟨.inl v, hv.resolve_left (fun unmarked => unmarked marked), fun g hg => ?_⟩
    rcases centered g hg.1 with a | b
    · exact Or.inl (by rw [a]; simp [splitEndpoint, marked])
    · exact Or.inr (by rw [b]; simp [splitEndpoint, marked])
  have transfer := project_fold R (start Z) (splitStart R W) T T
    (fun h => (not_all_initial Z h).elim)
    (fun r hr => ⟨liftOperand r hr r.1 (Or.inl rfl), liftOperand r hr r.2 (Or.inr rfl)⟩)
    (hR Z origCover)
  simpa only [Set.inter_self] using transfer

end CoverUnion4653
