import Mathlib

namespace LeafOrElimination

abbrev Signal (V : Type*) := (V → Bool) → Bool

section Restriction

variable {V : Type*} [DecidableEq V] (leaf : V)

def zeroAt (x : V → Bool) : V → Bool := Function.update x leaf false

def Depends (s : Signal V) : Prop := ∃ x, s x ≠ s (zeroAt leaf x)

def Survives (s : Signal V) : Prop := ∃ x, s (zeroAt leaf x) = true

def Escapes (s : Signal V) : Prop := Depends leaf s ∧ Survives leaf s

theorem depends_binary (op : Bool → Bool → Bool) (a b : Signal V)
    (dep : Depends leaf (fun x => op (a x) (b x))) : Depends leaf a ∨ Depends leaf b := by
  classical
  obtain ⟨x, neq⟩ := dep
  by_cases h : a x = a (zeroAt leaf x)
  · exact Or.inr ⟨x, fun k => neq (congrArg₂ op h k)⟩
  · exact Or.inl ⟨x, h⟩

theorem and_escape (a b : Signal V) (esc : Escapes leaf (fun x => a x && b x)) :
    Escapes leaf a ∨ Escapes leaf b := by
  obtain ⟨dep, x, yes⟩ := esc
  have alive : a (zeroAt leaf x) = true ∧ b (zeroAt leaf x) = true := by simpa using yes
  rcases depends_binary leaf Bool.and a b dep with h | h
  · exact Or.inl ⟨h, x, alive.1⟩
  · exact Or.inr ⟨h, x, alive.2⟩

theorem zero_of_depends_of_no_escape {s : Signal V} (dep : Depends leaf s) (no : ¬ Escapes leaf s) :
    ∀ x, s (zeroAt leaf x) = false := by
  intro x
  cases h : s (zeroAt leaf x)
  · rfl
  · exact (no ⟨dep, x, h⟩).elim

end Restriction

inductive Op where
  | and | or
  deriving DecidableEq

def Op.run : Op → Bool → Bool → Bool
  | .and => Bool.and
  | .or => Bool.or

structure Gate where
  op : Op
  left : ℕ
  right : ℕ

def Gate.eval {V : Type*} (g : Gate) (w : ℕ → Signal V) : Signal V :=
  fun x => g.op.run (w g.left x) (w g.right x)

/-- The latest gate is first in the list. Gates read the environment of their suffix. -/
def wire {V : Type*} (input : ℕ → Signal V) (base : ℕ) : List Gate → ℕ → Signal V
  | [], i => if i < base then input i else fun _ => false
  | g :: earlier, i => if i = base + earlier.length then g.eval (wire input base earlier)
    else wire input base earlier i

theorem first_escaping_or {V : Type*} [DecidableEq V] (leaf : V)
    (input : ℕ → Signal V) (base : ℕ)
    (sources : ∀ j < base, ¬ Escapes leaf (input j))
    (R : List Gate) (i : ℕ) (esc : Escapes leaf (wire input base R i)) :
    ∃ later g earlier, R = later ++ g :: earlier ∧ g.op = .or ∧
      ((∀ x, wire input base earlier g.left (zeroAt leaf x) = false) ∨
       (∀ x, wire input base earlier g.right (zeroAt leaf x) = false)) := by
  classical
  induction R generalizing i with
  | nil =>
    by_cases h : i < base
    · exact (sources i h (by simpa [wire, h] using esc)).elim
    · simp [wire, h, Escapes, Depends] at esc
  | cons g earlier ih =>
    have lift (j : ℕ) (ej : Escapes leaf (wire input base earlier j)) :
        ∃ later p prior, g :: earlier = later ++ p :: prior ∧ p.op = .or ∧
          ((∀ x, wire input base prior p.left (zeroAt leaf x) = false) ∨
           (∀ x, wire input base prior p.right (zeroAt leaf x) = false)) := by
      obtain ⟨later, p, prior, eq, hor, zero⟩ := ih j ej
      exact ⟨g :: later, p, prior, congrArg (List.cons g) eq, hor, zero⟩
    by_cases current : i = base + earlier.length
    · have ge : Escapes leaf (g.eval (wire input base earlier)) := by simpa [wire, current] using esc
      change Escapes leaf (fun x => g.op.run (wire input base earlier g.left x)
        (wire input base earlier g.right x)) at ge
      by_cases left : Escapes leaf (wire input base earlier g.left)
      · exact lift g.left left
      by_cases right : Escapes leaf (wire input base earlier g.right)
      · exact lift g.right right
      cases hg : g.op with
      | and =>
        have escape := and_escape leaf (wire input base earlier g.left) (wire input base earlier g.right)
          (by simpa only [hg, Op.run] using ge)
        exact (escape.elim left right).elim
      | or =>
        have dep := depends_binary leaf Bool.or (wire input base earlier g.left)
          (wire input base earlier g.right) (by simpa only [hg, Op.run] using ge.1)
        exact ⟨[], g, earlier, rfl, hg, dep.imp
          (fun h => zero_of_depends_of_no_escape leaf h left)
          (fun h => zero_of_depends_of_no_escape leaf h right)⟩
    · exact lift i (by simpa [wire, current] using esc)

def orCount (R : List Gate) : ℕ := R.countP (fun g => decide (g.op = .or))

theorem replay {V : Type*} (input : ℕ → Signal V) (base : ℕ) (x : V → Bool)
    (a b : List Gate) (length : a.length = b.length)
    (same : ∀ i, wire input base a i x = wire input base b i x)
    (later : List Gate) : ∀ i, wire input base (later ++ a) i x = wire input base (later ++ b) i x := by
  induction later with
  | nil => exact same
  | cons g tail ih =>
    intro i
    have count : (tail ++ a).length = (tail ++ b).length := by simp [length]
    simp only [List.cons_append, wire, count]
    split <;> simp [Gate.eval, ih]

theorem save_one_or {V : Type*} [DecidableEq V] (leaf : V)
    (input : ℕ → Signal V) (base : ℕ)
    (sources : ∀ j < base, ¬ Escapes leaf (input j))
    (R : List Gate) (i : ℕ) (esc : Escapes leaf (wire input base R i)) :
    ∃ Q : List Gate, Q.length = R.length ∧ orCount Q + 1 = orCount R ∧
      ∀ x, wire input base Q i (zeroAt leaf x) = wire input base R i (zeroAt leaf x) := by
  obtain ⟨later, g, earlier, rfl, hor, zero⟩ := first_escaping_or leaf input base sources R i esc
  have replace (p : ℕ) (same : ∀ x, wire input base earlier p (zeroAt leaf x) =
      g.eval (wire input base earlier) (zeroAt leaf x)) :
      ∃ Q : List Gate, Q.length = (later ++ g :: earlier).length ∧
        orCount Q + 1 = orCount (later ++ g :: earlier) ∧
        ∀ x, wire input base Q i (zeroAt leaf x) = wire input base (later ++ g :: earlier) i (zeroAt leaf x) := by
    let copy : Gate := ⟨.and, p, p⟩
    refine ⟨later ++ copy :: earlier, by simp, ?_, ?_⟩
    · simp [orCount, List.countP_append, hor, copy, Nat.add_assoc]
    · intro x
      apply replay input base (zeroAt leaf x) (copy :: earlier) (g :: earlier) rfl _ later i
      intro j
      by_cases current : j = base + earlier.length
      · simpa [wire, current, Gate.eval, copy, Op.run] using same x
      · simp [wire, current]
  rcases zero with left | right
  · exact replace g.right (fun x => by simp [Gate.eval, hor, Op.run, left x])
  · exact replace g.left (fun x => by simp [Gate.eval, hor, Op.run, right x])

section Edges

variable {V : Type*} [DecidableEq V]

noncomputable def edgeSignal (E : Finset (Finset V)) : Signal V := by
  classical exact fun x => decide (∃ e ∈ E, ∀ v ∈ e, x v = true)

omit [DecidableEq V] in
theorem edgeSignal_true (E : Finset (Finset V)) (x : V → Bool) :
    edgeSignal E x = true ↔ ∃ e ∈ E, ∀ v ∈ e, x v = true := by
  classical simp [edgeSignal]

def removeStar (E : Finset (Finset V)) (v : V) : Finset (Finset V) := E.filter (v ∉ ·)

theorem vertex_restriction (E : Finset (Finset V)) (v : V) (x : V → Bool) :
    edgeSignal E (zeroAt v x) = edgeSignal (removeStar E v) x := by
  have equiv : edgeSignal E (zeroAt v x) = true ↔ edgeSignal (removeStar E v) x = true := by
    rw [edgeSignal_true, edgeSignal_true]
    constructor
    · rintro ⟨f, hf, yes⟩
      have off : v ∉ f := fun h => by simpa [zeroAt] using yes v h
      exact ⟨f, Finset.mem_filter.mpr ⟨hf, off⟩, fun u hu => by
        have diff : u ≠ v := fun eq => off (eq ▸ hu)
        simpa [zeroAt, Function.update_of_ne diff] using yes u hu⟩
    · rintro ⟨f, hf, yes⟩
      obtain ⟨mem, off⟩ := Finset.mem_filter.mp hf
      refine ⟨f, mem, fun u hu => ?_⟩
      have diff : u ≠ v := fun eq => off (eq ▸ hu)
      simpa [zeroAt, Function.update_of_ne diff] using yes u hu
  cases a : edgeSignal E (zeroAt v x) <;> cases b : edgeSignal (removeStar E v) x <;> simp_all

theorem vertex_escapes (E : Finset (Finset V)) (e : Finset V) (v : V)
    (edges : ∀ f ∈ E, f.card = 2) (he : e ∈ E) (hasVertex : v ∈ e)
    (remain : (removeStar E v).Nonempty) : Escapes v (edgeSignal E) := by
  classical
  constructor
  · let onEdge : V → Bool := fun v => decide (v ∈ e)
    have pos : edgeSignal E onEdge = true := (edgeSignal_true ..).mpr ⟨e, he, by simp [onEdge]⟩
    refine ⟨onEdge, fun same => ?_⟩
    rw [vertex_restriction E v] at same
    obtain ⟨f, hf, live⟩ := (edgeSignal_true _ onEdge).mp (same.symm.trans pos)
    obtain ⟨mem, off⟩ := Finset.mem_filter.mp hf
    have sub : f ⊆ e := fun u hu => by simpa [onEdge] using live u hu
    have eq : f = e := Finset.eq_of_subset_of_card_le sub (by rw [edges e he, edges f mem])
    exact off (eq.symm ▸ hasVertex)
  · obtain ⟨f, hf⟩ := remain
    let onEdge : V → Bool := fun v => decide (v ∈ f)
    exact ⟨onEdge, (vertex_restriction E v onEdge).trans
      ((edgeSignal_true ..).mpr ⟨f, hf, by simp [onEdge]⟩)⟩

def Primitive (s : Signal V) : Prop := (∃ b, s = (fun _ => b)) ∨ ∃ v, s = (fun x => x v)

theorem primitive_not_escape (leaf : V) (s : Signal V) (h : Primitive s) : ¬ Escapes leaf s := by
  rcases h with ⟨b, rfl⟩ | ⟨v, rfl⟩
  · simp [Escapes, Depends]
  · by_cases eq : v = leaf
    · subst v
      simp [Escapes, Survives, zeroAt]
    · simp [Escapes, Depends, zeroAt, Function.update_of_ne eq]

theorem primitive_restrict (leaf : V) (s : Signal V) (h : Primitive s) :
    Primitive (fun x => s (zeroAt leaf x)) := by
  rcases h with ⟨b, rfl⟩ | ⟨v, rfl⟩
  · exact Or.inl ⟨b, rfl⟩
  · by_cases eq : v = leaf
    · subst v
      exact Or.inl ⟨false, by funext x; simp [zeroAt]⟩
    · exact Or.inr ⟨v, by funext x; simp [zeroAt, Function.update_of_ne eq]⟩

theorem restrict_input (leaf : V) (input : ℕ → Signal V) (base : ℕ) (R : List Gate) (x : V → Bool) :
    ∀ j, wire (fun k y => input k (zeroAt leaf y)) base R j x = wire input base R j (zeroAt leaf x) := by
  induction R with
  | nil => intro j; by_cases h : j < base <;> simp [wire, h]
  | cons g tail ih => intro j; simp only [wire]; split <;> simp [Gate.eval, ih]

theorem remove_vertex_cost (E : Finset (Finset V)) (e : Finset V) (v : V)
    (edges : ∀ f ∈ E, f.card = 2) (he : e ∈ E) (hasVertex : v ∈ e)
    (remain : (removeStar E v).Nonempty)
    (input : ℕ → Signal V) (base : ℕ) (sources : ∀ j < base, Primitive (input j))
    (R : List Gate) (i : ℕ) (computes : wire input base R i = edgeSignal E) :
    ∃ (Q : List Gate) (next : ℕ → Signal V), orCount Q + 1 = orCount R ∧
      (∀ j < base, Primitive (next j)) ∧ wire next base Q i = edgeSignal (removeStar E v) := by
  have esc : Escapes v (wire input base R i) := computes ▸ vertex_escapes E e v edges he hasVertex remain
  obtain ⟨Q, _, cost, equal⟩ := save_one_or v input base (fun j hj => primitive_not_escape v _ (sources j hj))
    R i esc
  refine ⟨Q, (fun j x => input j (zeroAt v x)), cost, fun j hj => primitive_restrict v _ (sources j hj), ?_⟩
  funext x
  rw [restrict_input, equal, computes, vertex_restriction E v]

theorem peel_one_edge (E : Finset (Finset V)) (e : Finset V) (leaf : V)
    (edges : ∀ f ∈ E, f.card = 2) (he : e ∈ E) (hasLeaf : leaf ∈ e)
    (unique : ∀ f ∈ E, leaf ∈ f → f = e) (remain : (E.erase e).Nonempty)
    (input : ℕ → Signal V) (base : ℕ) (sources : ∀ j < base, Primitive (input j))
    (R : List Gate) (i : ℕ) (computes : wire input base R i = edgeSignal E) :
    ∃ (Q : List Gate) (next : ℕ → Signal V), orCount Q + 1 = orCount R ∧
      (∀ j < base, Primitive (next j)) ∧ wire next base Q i = edgeSignal (E.erase e) := by
  have eq : removeStar E leaf = E.erase e := by
    ext f
    rw [removeStar, Finset.mem_filter, Finset.mem_erase]
    exact ⟨fun ⟨mem, off⟩ => ⟨fun h => off (h.symm ▸ hasLeaf), mem⟩,
      fun ⟨ne, mem⟩ => ⟨mem, fun h => ne (unique f mem h)⟩⟩
  rw [← eq] at remain ⊢
  exact remove_vertex_cost E e leaf edges he hasLeaf remain input base sources R i computes

/-- A finite certificate of leaf deletions, ending before the final edge is removed. -/
inductive Peels : Finset (Finset V) → Finset (Finset V) → ℕ → Prop where
  | done (E) : Peels E E 0
  | next {E core : Finset (Finset V)} {k : ℕ} (e : Finset V) (leaf : V)
      (he : e ∈ E) (hasLeaf : leaf ∈ e) (unique : ∀ f ∈ E, leaf ∈ f → f = e)
      (remain : (E.erase e).Nonempty) (tail : Peels (E.erase e) core k) : Peels E core (k + 1)

theorem peel_to_core {E core : Finset (Finset V)} {k : ℕ} (p : Peels E core k)
    (edges : ∀ f ∈ E, f.card = 2) (input : ℕ → Signal V) (base : ℕ)
    (sources : ∀ j < base, Primitive (input j)) (R : List Gate) (i : ℕ)
    (computes : wire input base R i = edgeSignal E) :
    ∃ (Q : List Gate) (next : ℕ → Signal V), orCount Q + k = orCount R ∧
      (∀ j < base, Primitive (next j)) ∧ wire next base Q i = edgeSignal core := by
  induction p generalizing input R with
  | done => exact ⟨R, input, by simp, sources, computes⟩
  | next e leaf he hasLeaf unique remain tail ih =>
    obtain ⟨M, middle, saved, sm, cm⟩ := peel_one_edge _ e leaf edges he hasLeaf unique remain
      input base sources R i computes
    obtain ⟨Q, next, cost, sq, cq⟩ := ih (fun f hf => edges f (Finset.mem_erase.mp hf).2) middle sm M cm
    exact ⟨Q, next, by omega, sq, cq⟩

/-- Each deleted vertex has a surviving neighbor, and some edge survives its deletion. -/
def ValidSchedule (E : Finset (Finset V)) : List V → Prop
  | [] => True
  | v :: rest => (∃ e ∈ E, v ∈ e) ∧ (removeStar E v).Nonempty ∧ ValidSchedule (removeStar E v) rest

instance (E : Finset (Finset V)) (order : List V) : Decidable (ValidSchedule E order) := by
  induction order generalizing E with
  | nil => exact isTrue trivial
  | cons v tail ih =>
    letI := ih (removeStar E v)
    unfold ValidSchedule
    infer_instance

theorem schedule_lower_bound (E : Finset (Finset V)) (order : List V) (valid : ValidSchedule E order)
    (edges : ∀ f ∈ E, f.card = 2) (input : ℕ → Signal V) (base : ℕ)
    (sources : ∀ j < base, Primitive (input j)) (R : List Gate) (i : ℕ)
    (computes : wire input base R i = edgeSignal E) : order.length ≤ orCount R := by
  induction order generalizing E input R with
  | nil => simp
  | cons v order ih =>
    obtain ⟨⟨e, he, hv⟩, remain, tail⟩ := valid
    obtain ⟨M, middle, saved, sm, cm⟩ := remove_vertex_cost E e v edges he hv remain input base sources R i computes
    have cost := ih (removeStar E v) tail (fun f hf => edges f (Finset.mem_filter.mp hf).1) middle sm M cm
    simp only [List.length_cons]
    omega

end Edges

namespace PG4

abbrev Vertex := Fin 42

def incidence (a b : Vertex) : Prop :=
  a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)

instance (a b : Vertex) : Decidable (incidence a b) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def edges : Finset (Finset Vertex) :=
  (((Finset.univ : Finset Vertex) ×ˢ (Finset.univ : Finset Vertex)).filter
    (fun e => incidence e.1 e.2)).image fun e => {e.1, e.2}

def order : List Vertex :=
  [37, 36, 33, 23, 40, 35, 34, 31, 32, 30, 25, 24, 39, 29, 27, 22, 20, 15, 13, 3,
   18, 17, 12, 10, 11, 8, 7, 2, 19, 9, 6, 5, 16, 14, 4, 1, 41, 38, 28, 26]

theorem all_pairs : ∀ e ∈ edges, e.card = 2 := by
  intro e he
  obtain ⟨⟨u, v⟩, member, rfl⟩ := Finset.mem_image.mp he
  have sides := (Finset.mem_filter.mp member).2
  have distinct : u ≠ v := fun eq => by subst v; exact (Nat.not_lt_of_ge sides.2.1) sides.1
  simp [distinct]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem order_valid : ValidSchedule edges order := by decide +kernel

theorem lower_bound_40 (input : ℕ → Signal Vertex) (base : ℕ)
    (sources : ∀ j < base, Primitive (input j)) (R : List Gate) (i : ℕ)
    (computes : wire input base R i = edgeSignal edges) : 40 ≤ orCount R :=
  schedule_lower_bound edges order order_valid all_pairs input base sources R i computes

end PG4

end LeafOrElimination
