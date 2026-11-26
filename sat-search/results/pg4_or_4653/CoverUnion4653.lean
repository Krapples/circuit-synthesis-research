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
  have isCover : ∀ e : Edge, incidence e → selected e.1 ∨ selected e.2 := by decide +kernel
  have privateCount : ∀ v : Vertex, selected v →
      (privateEdges.filter fun e => e.1 = v ∨ e.2 = v).card ≤ 1 := by decide +kernel
  have hP : ∀ e ∈ privateEdges, incidence e := by decide +kernel
  have hcard : privateEdges.card = 34 := by decide +kernel
  have init : Consistent privateEdges (start {v | selected v}) id := by
    intro S hS a ha b hb ha' hb'
    rcases hS with empty | ⟨v, hv, hv'⟩
    · exact (empty ▸ ha').elim
    · exact Finset.card_le_one.mp (privateCount v hv) a
        (Finset.mem_filter.mpr ⟨ha, hv' a ha'⟩) b (Finset.mem_filter.mpr ⟨hb, hv' b hb'⟩)
  have lower := private_edge_lower_bound privateEdges _ R init {e | incidence e}
    (fun _ he => hP _ he) (hR {v | selected v} isCover)
  omega

end CoverUnion4653
