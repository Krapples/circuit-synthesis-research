import ConjunctionCompiler
import LeafOrElimination

namespace CompilerBridge

open ConjunctionCompiler (Signal)

def reverseGate (g : ConjunctionCompiler.Gate) : LeafOrElimination.Gate :=
  ⟨if g.isOr then .or else .and, g.left, g.right⟩

theorem eval_length {V : Type*} (start : List (Signal V)) (R : List ConjunctionCompiler.Gate) :
    (ConjunctionCompiler.eval start R).length = start.length + R.length := by
  induction R generalizing start with
  | nil => simp [ConjunctionCompiler.eval]
  | cons g tail ih =>
    change (ConjunctionCompiler.eval (start ++ [g.eval start]) tail).length = _
    rw [ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem ref_append_singleton {V : Type*} (wires : List (Signal V)) (s : Signal V) (i : ℕ) :
    ConjunctionCompiler.ref (wires ++ [s]) i =
      if i = wires.length then s else ConjunctionCompiler.ref wires i := by
  by_cases newest : i = wires.length
  · subst i
    simpa using ConjunctionCompiler.ref_last wires s
  · rw [ite_eq_right newest]
    by_cases old : i < wires.length
    · simp [ConjunctionCompiler.ref, List.getElem?_append_left old]
    · have after : (wires ++ [s]).length ≤ i := by simp; omega
      simp [ConjunctionCompiler.ref, List.getElem?_eq_none after, List.getElem?_eq_none (by omega : wires.length ≤ i)]

theorem gate_matches {V : Type*} (g : ConjunctionCompiler.Gate) (wires : List (Signal V)) :
    (reverseGate g).eval (ConjunctionCompiler.ref wires) = g.eval wires := by
  funext x
  cases flag : g.isOr <;>
    simp [reverseGate, LeafOrElimination.Gate.eval, LeafOrElimination.Op.run, ConjunctionCompiler.Gate.eval,
      ConjunctionCompiler.ref, flag]

theorem reverse_matches {V : Type*} (start : List (Signal V)) (rev : List ConjunctionCompiler.Gate) :
    ∀ i, LeafOrElimination.wire (ConjunctionCompiler.ref start) start.length (rev.map reverseGate) i =
      ConjunctionCompiler.ref (ConjunctionCompiler.eval start rev.reverse) i := by
  induction rev with
  | nil =>
    intro i
    by_cases old : i < start.length
    · simp [LeafOrElimination.wire, ConjunctionCompiler.eval, old]
    · simp [LeafOrElimination.wire, ConjunctionCompiler.eval, ConjunctionCompiler.ref, old]
  | cons g tail ih =>
    intro i
    let wires := ConjunctionCompiler.eval start tail.reverse
    have len : wires.length = start.length + tail.length := by
      simp [wires, eval_length]
    simp only [List.map_cons, LeafOrElimination.wire, List.length_map, List.reverse_cons,
      ConjunctionCompiler.eval_append]
    change (if i = start.length + tail.length then _ else _) =
      ConjunctionCompiler.ref (wires ++ [g.eval wires]) i
    rw [ref_append_singleton, len]
    split
    · rw [funext ih, gate_matches]
    · exact ih i

theorem reverse_cost (rev : List ConjunctionCompiler.Gate) :
    LeafOrElimination.orCount (rev.map reverseGate) = ConjunctionCompiler.orCount rev.reverse := by
  induction rev with
  | nil => rfl
  | cons g tail ih =>
    have flag : decide ((reverseGate g).op = .or) = g.isOr := by
      cases h : g.isOr <;> simp [reverseGate, h]
    change (List.countP (fun g => decide (g.op = .or)) (reverseGate g :: tail.map reverseGate)) = _
    simp only [List.countP_cons, flag, List.reverse_cons, ConjunctionCompiler.orCount_append]
    change (LeafOrElimination.orCount (tail.map reverseGate) + (if g.isOr then 1 else 0)) =
      ConjunctionCompiler.orCount tail.reverse + ConjunctionCompiler.orCount [g]
    rw [ih]
    cases h : g.isOr <;> simp [ConjunctionCompiler.orCount, h]

theorem transfer_lower_bound {V : Type*} (start : List (Signal V)) (f : Signal V) (bound : ℕ)
    (lower : ∀ R i, LeafOrElimination.wire (ConjunctionCompiler.ref start) start.length R i = f →
      bound ≤ LeafOrElimination.orCount R) (gates : List ConjunctionCompiler.Gate) (i : ℕ)
    (computes : ConjunctionCompiler.ref (ConjunctionCompiler.eval start gates) i = f) :
    bound ≤ ConjunctionCompiler.orCount gates := by
  have eq := reverse_matches start gates.reverse i
  rw [List.reverse_reverse] at eq
  have count := reverse_cost gates.reverse
  rw [List.reverse_reverse] at count
  rw [← count]
  exact lower _ i (eq.trans computes)

namespace PG4

abbrev Vertex := LeafOrElimination.PG4.Vertex
abbrev Edge := Vertex × Vertex

def incidenceSet : Set Edge := {p | LeafOrElimination.PG4.incidence p.1 p.2}

theorem graph_signal_matches : ConjunctionCompiler.edgeSignal (id : Edge → Vertex × Vertex) incidenceSet =
    LeafOrElimination.edgeSignal LeafOrElimination.PG4.edges := by
  classical
  funext x
  have sameTruth : ConjunctionCompiler.edgeSignal (id : Edge → Vertex × Vertex) incidenceSet x = true ↔
      LeafOrElimination.edgeSignal LeafOrElimination.PG4.edges x = true := by
    simp only [ConjunctionCompiler.edgeSignal, decide_eq_true_eq, id_eq, LeafOrElimination.edgeSignal_true]
    constructor
    · rintro ⟨p, hp, a, b⟩
      refine ⟨{p.1, p.2}, ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨by simp, hp⟩, rfl⟩
      · intro v hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl <;> assumption
    · rintro ⟨e, he, h⟩
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
      exact ⟨p, (Finset.mem_filter.mp hp).2, h p.1 (by simp), h p.2 (by simp)⟩
  cases a : ConjunctionCompiler.edgeSignal (id : Edge → Vertex × Vertex) incidenceSet x <;>
    cases b : LeafOrElimination.edgeSignal LeafOrElimination.PG4.edges x <;> simp_all

def seed : List (Signal Vertex) :=
  (fun _ => false) :: (fun _ => true) :: List.ofFn (fun (i : Vertex) x => x i)

theorem seed_length : seed.length = 44 := by simp [seed]

theorem seed_vertex (v : Vertex) : ConjunctionCompiler.ref seed (v.val + 2) = fun x => x v := by
  change ((List.ofFn (fun (i : Vertex) (x : Vertex → Bool) => x i))[v.val]?).getD (fun _ => false) = _
  rw [List.getElem?_ofFn, dif_pos v.isLt]
  rfl

theorem seed_primitives (i : ℕ) (valid : i < seed.length) :
    LeafOrElimination.Primitive (ConjunctionCompiler.ref seed i) := by
  match i with
  | 0 => exact Or.inl ⟨false, rfl⟩
  | 1 => exact Or.inl ⟨true, rfl⟩
  | n + 2 =>
    have h : n < 42 := by rw [seed_length] at valid; omega
    exact Or.inr ⟨⟨n, h⟩, seed_vertex ⟨n, h⟩⟩

theorem lower_bound_common_union (R : List (Set Edge × Set Edge))
    (common : ∀ x, (∀ e ∈ incidenceSet, ConjunctionCompiler.covered id x e) →
      incidenceSet ∈ R.foldl ConjunctionCompiler.unionStep (ConjunctionCompiler.stars id x)) :
    40 ≤ R.length := by
  have vertexValid (v : Vertex) : v.val + 2 < seed.length := by
    rw [seed_length]
    have h := v.isLt
    omega
  obtain ⟨gates, out, cost, _, computes⟩ := ConjunctionCompiler.compile_finite_cover_union id R incidenceSet common
    seed (fun v => v.val + 2) vertexValid seed_vertex 0 (by simp [seed_length]) rfl 1 (by simp [seed_length]) rfl
  rw [← cost]
  apply transfer_lower_bound seed (LeafOrElimination.edgeSignal LeafOrElimination.PG4.edges) 40
  · exact LeafOrElimination.PG4.lower_bound_40 (ConjunctionCompiler.ref seed) seed.length seed_primitives
  · exact computes.trans graph_signal_matches

end PG4

end CompilerBridge
