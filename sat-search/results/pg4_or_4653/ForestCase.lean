import CompilerBridge
import CoverUnion4653
import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace ForestCase

open LeafOrElimination (Peels)

section FiniteForest

variable {V : Type*} [Fintype V] [DecidableEq V]

def graphOf (E : Finset (Finset V)) : SimpleGraph V where
  Adj a b := a ≠ b ∧ {a, b} ∈ E
  symm := ⟨fun {a b} h => ⟨h.1.symm, by simpa [Finset.pair_comm] using h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

omit [DecidableEq V] in
theorem exists_leaf (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsAcyclic)
    {a b : V} (ab : G.Adj a b) : ∃ v, ∃! w, G.Adj v w := by
  classical
  let C := G.connectedComponentMk a
  have ha : a ∈ C.supp := by simp [C]
  have hb : b ∈ C.supp := C.mem_supp_of_adj_mem_supp ha ab
  let : Nontrivial C := ⟨⟨a, ha⟩, ⟨b, hb⟩, fun eq => G.ne_of_adj ab (congrArg Subtype.val eq)⟩
  let : Fintype C := Fintype.ofFinite C
  let : DecidableRel C.toSimpleGraph.Adj := fun _ _ => Classical.propDecidable _
  obtain ⟨v, degree⟩ := (hG.isTree_connectedComponent C).exists_vert_degree_one_of_nontrivial
  obtain ⟨w, vw, unique⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp degree
  refine ⟨v.val, w.val, vw, fun u vu => ?_⟩
  have hu : u ∈ C.supp := C.mem_supp_of_adj_mem_supp v.property vu
  exact congrArg Subtype.val (unique ⟨u, hu⟩ vu)

theorem forest_has_leaf (E : Finset (Finset V)) (pairs : ∀ f ∈ E, f.card = 2)
    (acyclic : (graphOf E).IsAcyclic) (nonempty : E.Nonempty) :
    ∃ v, ∃! e, e ∈ E ∧ v ∈ e := by
  classical
  obtain ⟨f, hf⟩ := nonempty
  obtain ⟨a, b, ab, rfl⟩ := Finset.card_eq_two.mp (pairs f hf)
  let : DecidableRel (graphOf E).Adj := fun _ _ => Classical.propDecidable _
  obtain ⟨v, w, vw, only⟩ := exists_leaf (graphOf E) acyclic (show (graphOf E).Adj a b from ⟨ab, hf⟩)
  refine ⟨v, {v,w}, ⟨vw.2, by simp⟩, fun g ⟨hg, hvg⟩ => ?_⟩
  obtain ⟨c, d, cd, rfl⟩ := Finset.card_eq_two.mp (pairs g hg)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hvg
  rcases hvg with eq | eq
  · subst c
    exact congrArg (fun t => ({v, t} : Finset V)) (only d ⟨cd, hg⟩)
  · subst d
    have hvc : (graphOf E).Adj v c := ⟨cd.symm, by simpa [Finset.pair_comm] using hg⟩
    rw [Finset.pair_comm c v, only c hvc]

omit [Fintype V] in
theorem peel_until_core (E : Finset (Finset V)) (nonempty : E.Nonempty) :
    ∃ core k, core ⊆ E ∧ core.Nonempty ∧ core.card + k = E.card ∧ Peels E core k ∧
      (core.card = 1 ∨ ¬ ∃ v, ∃! e, e ∈ core ∧ v ∈ e) := by
  classical
  revert nonempty
  refine E.strongInductionOn ?_
  intro E ih nonempty
  by_cases small : E.card = 1
  · exact ⟨E, 0, by rfl, nonempty, by simp, Peels.done E, Or.inl small⟩
  by_cases leaf : ∃ v, ∃! e, e ∈ E ∧ v ∈ e
  · obtain ⟨v, e, ⟨he, hv⟩, unique⟩ := leaf
    have edges : (E.erase e).card + 1 = E.card := Finset.card_erase_add_one he
    have remain : (E.erase e).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨core, k, sub, coreNonempty, size, trace, final⟩ := ih (E.erase e) (Finset.erase_ssubset he) remain
    exact ⟨core, k + 1, sub.trans (Finset.erase_subset _ _), coreNonempty, by omega,
      Peels.next e v he hv (fun f hf hvf => unique f ⟨hf,hvf⟩) remain trace, final⟩
  · exact ⟨E, 0, by rfl, nonempty, by simp, Peels.done E, Or.inr leaf⟩

theorem forest_peels (E : Finset (Finset V)) (pairs : ∀ f ∈ E, f.card = 2)
    (acyclic : (graphOf E).IsAcyclic) (nonempty : E.Nonempty) :
    ∃ core, Peels E core (E.card - 1) := by
  obtain ⟨core, k, sub, coreNonempty, size, trace, final⟩ := peel_until_core E nonempty
  have mono : graphOf core ≤ graphOf E := fun _ _ h => ⟨h.1, sub h.2⟩
  have one : core.card = 1 := final.resolve_right (fun no =>
    no (forest_has_leaf core (fun f hf => pairs f (sub hf)) (acyclic.anti mono) coreNonempty))
  have count : k = E.card - 1 := by omega
  exact ⟨core, count ▸ trace⟩

theorem forest_or_lower_bound (E : Finset (Finset V)) (pairs : ∀ f ∈ E, f.card = 2)
    (acyclic : (graphOf E).IsAcyclic) (nonempty : E.Nonempty)
    (input : ℕ → LeafOrElimination.Signal V) (base : ℕ)
    (sources : ∀ j < base, LeafOrElimination.Primitive (input j))
    (R : List LeafOrElimination.Gate) (i : ℕ)
    (computes : LeafOrElimination.wire input base R i = LeafOrElimination.edgeSignal E) :
    E.card - 1 ≤ LeafOrElimination.orCount R := by
  obtain ⟨core, certificate⟩ := forest_peels E pairs acyclic nonempty
  obtain ⟨Q, _, cost, _, _⟩ := LeafOrElimination.peel_to_core certificate pairs input base sources R i computes
  omega

end FiniteForest

theorem acyclic_of_acyclic_induce {V : Type*} (G : SimpleGraph V) (keep : Set V)
    (core : (G.induce keep).IsAcyclic)
    (leaves : ∀ v ∉ keep, (G.neighborSet v).Subsingleton) : G.IsAcyclic := by
  classical
  intro u p cyc
  have supported (x : V) (hx : x ∈ p.support) : x ∈ keep := by
    by_contra off
    by_cases eq : x = u
    · subst x
      have edge : G.Adj u p.snd := p.adj_snd (fun h => cyc.ne_nil h.eq_nil)
      have hs : p.snd ∈ p.support := by cases p <;> simp_all
      have rotated := (SimpleGraph.Walk.isCycle_rotate hs).mpr cyc
      have hu : u ∈ (p.rotate p.snd hs).support := (p.mem_support_rotate_iff p.snd hs).mpr p.start_mem_support
      exact rotated.isTrail.notMem_support_of_subsingleton_neighborSet
        (G.ne_of_adj edge) (G.ne_of_adj edge) (leaves u off) hu
    · exact cyc.isTrail.notMem_support_of_subsingleton_neighborSet eq eq (leaves x off) hx
  exact core (p.induce keep supported) (SimpleGraph.Walk.isCycle_induce.mpr cyc)

namespace PG4

open CoverUnion4653 (Vertex Edge SplitVertex incidence allEdges operandCenters splitEndpoint)

def collapse : SplitVertex → Vertex
  | .inl v => v
  | .inr (_, v) => v

theorem collapse_endpoint (R : List (Set Edge × Set Edge)) (e : Edge) (v : Vertex) :
    collapse (splitEndpoint R e v) = v := by
  classical
  by_cases marked : v ∈ operandCenters R <;> simp [splitEndpoint, collapse, marked]

noncomputable def splitPair (R : List (Set Edge × Set Edge)) (e : Edge) : Finset SplitVertex :=
  {splitEndpoint R e e.1, splitEndpoint R e e.2}

noncomputable def splitEdges (R : List (Set Edge × Set Edge)) : Finset (Finset SplitVertex) :=
  allEdges.image (splitPair R)

def originalEdges : Finset (Finset Vertex) := allEdges.image (fun e => {e.1, e.2})

theorem split_pairs (R : List (Set Edge × Set Edge)) : ∀ f ∈ splitEdges R, f.card = 2 := by
  intro f hf
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hf
  have sides := (Finset.mem_filter.mp he).2
  have distinct : splitEndpoint R e e.1 ≠ splitEndpoint R e e.2 := fun eq => by
    have coord := congrArg collapse eq
    simp only [collapse_endpoint] at coord
    exact (Nat.not_lt_of_ge sides.2.1) (coord ▸ sides.1)
  simp [splitPair, distinct]

theorem split_card (R : List (Set Edge × Set Edge)) : (splitEdges R).card = 105 := by
  have cardinal : allEdges.card = 105 := by decide +kernel
  rw [splitEdges, Finset.card_image_of_injOn, cardinal]
  intro e he f hf eq
  have collapsed := congrArg (Finset.image collapse) eq
  have same : ({e.1, e.2} : Finset Vertex) = {f.1, f.2} := by
    simpa [splitPair, collapse_endpoint] using collapsed
  have eSides := (Finset.mem_filter.mp he).2
  have fSides := (Finset.mem_filter.mp hf).2
  have pMem : e.1 ∈ ({f.1, f.2} : Finset Vertex) := same ▸ (by simp : e.1 ∈ ({e.1, e.2} : Finset Vertex))
  have lMem : e.2 ∈ ({f.1, f.2} : Finset Vertex) := same ▸ (by simp : e.2 ∈ ({e.1, e.2} : Finset Vertex))
  simp only [Finset.mem_insert, Finset.mem_singleton] at pMem lMem
  refine Prod.ext (pMem.resolve_right fun h => ?_) (lMem.resolve_left fun h => ?_)
  · exact (Nat.not_lt_of_ge fSides.2.1) (h ▸ eSides.1)
  · exact (Nat.not_lt_of_ge eSides.2.1) (h.symm ▸ fSides.1)

def retained (R : List (Set Edge × Set Edge)) : Set SplitVertex :=
  {s | ∃ v ∈ operandCenters R, s = Sum.inl v}

theorem split_off_unique (R : List (Set Edge × Set Edge)) (s : SplitVertex) (off : s ∉ retained R)
    {A B : Finset SplitVertex} (ha : A ∈ splitEdges R) (hb : B ∈ splitEdges R)
    (sa : s ∈ A) (sb : s ∈ B) : A = B := by
  classical
  obtain ⟨e, _, he⟩ := Finset.mem_image.mp ha
  obtain ⟨f, _, hf⟩ := Finset.mem_image.mp hb
  have sE : s ∈ splitPair R e := he.symm ▸ sa
  have sF : s ∈ splitPair R f := hf.symm ▸ sb
  simp only [splitPair, Finset.mem_insert, Finset.mem_singleton] at sE sF
  obtain ⟨v, ev⟩ : ∃ v, s = splitEndpoint R e v := sE.elim (fun h => ⟨e.1,h⟩) (fun h => ⟨e.2,h⟩)
  obtain ⟨w, fw⟩ : ∃ w, s = splitEndpoint R f w := sF.elim (fun h => ⟨f.1,h⟩) (fun h => ⟨f.2,h⟩)
  have fresh : v ∉ operandCenters R := fun marked => off ⟨v, marked, by simpa [splitEndpoint, marked] using ev⟩
  have same := CoverUnion4653.splitEndpoint_fresh R e f v w fresh (ev.symm.trans fw)
  exact he.symm.trans (same ▸ hf)

theorem split_off_retained (R : List (Set Edge × Set Edge)) (s : SplitVertex) (off : s ∉ retained R) :
    ((graphOf (splitEdges R)).neighborSet s).Subsingleton := by
  intro t ht u hu
  change s ≠ t ∧ ({s,t} : Finset SplitVertex) ∈ splitEdges R at ht
  change s ≠ u ∧ ({s,u} : Finset SplitVertex) ∈ splitEdges R at hu
  have pairEq : ({s,t} : Finset SplitVertex) = {s,u} := split_off_unique R s off ht.2 hu.2 (by simp) (by simp)
  have tMem : t ∈ ({s,u} : Finset SplitVertex) := pairEq ▸ (by simp : t ∈ ({s,t} : Finset SplitVertex))
  simpa only [Finset.mem_insert, Finset.mem_singleton, ht.1.symm, false_or] using tMem

theorem retained_acyclic (R : List (Set Edge × Set Edge))
    (assm : ((graphOf originalEdges).induce (operandCenters R)).IsAcyclic) :
    (graphOf (splitEdges R)).IsAcyclic := by
  classical
  let toCore : retained R → operandCenters R := fun s =>
    ⟨collapse s.val, by obtain ⟨v, hv, eq⟩ := s.property; simpa [eq, collapse] using hv⟩
  have inj : Function.Injective toCore := by
    intro s t eq
    obtain ⟨v, _, sv⟩ := s.property
    obtain ⟨w, _, tw⟩ := t.property
    have vw : v = w := by
      have coord : collapse s.val = collapse t.val := congrArg Subtype.val eq
      simpa [sv, tw, collapse] using coord
    exact Subtype.ext (sv.trans (vw ▸ tw.symm))
  let mapCore : (graphOf (splitEdges R)).induce (retained R) →g (graphOf originalEdges).induce (operandCenters R) :=
    ⟨toCore, by
      intro s t adj
      change s.val ≠ t.val ∧ ({s.val,t.val} : Finset SplitVertex) ∈ splitEdges R at adj
      change collapse s.val ≠ collapse t.val ∧ ({collapse s.val,collapse t.val} : Finset Vertex) ∈ originalEdges
      refine ⟨fun eq => adj.1 (congrArg Subtype.val (inj (Subtype.ext eq))), ?_⟩
      obtain ⟨e, he, pairEq⟩ := Finset.mem_image.mp adj.2
      refine Finset.mem_image.mpr ⟨e, he, ?_⟩
      simpa [splitPair, collapse_endpoint] using congrArg (Finset.image collapse) pairEq⟩
  exact acyclic_of_acyclic_induce _ _ (assm.comap mapCore inj) (split_off_retained R)

noncomputable def finiteSeed (V : Type*) [Fintype V] : List (ConjunctionCompiler.Signal V) :=
  (fun _ => false) :: (fun _ => true) :: List.ofFn (fun i x => x ((Fintype.equivFin V).symm i))

theorem finite_seed_ref (V : Type*) [Fintype V] (i : Fin (Fintype.card V)) :
    ConjunctionCompiler.ref (finiteSeed V) (i.val + 2) = fun x => x ((Fintype.equivFin V).symm i) := by
  change ((List.ofFn (fun j (x : V → Bool) => x ((Fintype.equivFin V).symm j)))[i.val]?).getD
    (fun _ => false) = _
  rw [List.getElem?_ofFn, dite_eq_left i.isLt]
  rfl

theorem finite_seed_length (V : Type*) [Fintype V] : (finiteSeed V).length = Fintype.card V + 2 := by
  simp [finiteSeed, Nat.add_comm, Nat.add_left_comm]

theorem finite_seed_primitive (V : Type*) [Fintype V] (i : ℕ) (hi : i < (finiteSeed V).length) :
    LeafOrElimination.Primitive (ConjunctionCompiler.ref (finiteSeed V) i) := by
  match i with
  | 0 => exact Or.inl ⟨false, rfl⟩
  | 1 => exact Or.inl ⟨true, rfl⟩
  | j + 2 =>
    have hj : j < Fintype.card V := by rw [finite_seed_length] at hi; omega
    exact Or.inr ⟨_, finite_seed_ref V ⟨j,hj⟩⟩

noncomputable def endpoints (R : List (Set Edge × Set Edge)) (e : Edge) : SplitVertex × SplitVertex :=
  (splitEndpoint R e e.1, splitEndpoint R e e.2)

theorem split_signal (R : List (Set Edge × Set Edge)) :
    ConjunctionCompiler.edgeSignal (endpoints R) {e | incidence e} =
    LeafOrElimination.edgeSignal (splitEdges R) := by
  classical
  funext x
  have equiv : ConjunctionCompiler.edgeSignal (endpoints R) {e | incidence e} x = true ↔
      LeafOrElimination.edgeSignal (splitEdges R) x = true := by
    simp only [ConjunctionCompiler.edgeSignal, decide_eq_true_eq, LeafOrElimination.edgeSignal_true]
    constructor
    · rintro ⟨e, he, left, right⟩
      refine ⟨splitPair R e, Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨by simp, he⟩, rfl⟩, ?_⟩
      intro v hv
      simp only [splitPair, Finset.mem_insert, Finset.mem_singleton] at hv
      exact hv.elim (fun h => h.symm ▸ left) (fun h => h.symm ▸ right)
    · rintro ⟨f, hf, live⟩
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hf
      exact ⟨e, (Finset.mem_filter.mp he).2, live _ (by simp [splitPair, endpoints]),
        live _ (by simp [splitPair, endpoints])⟩
  cases a : ConjunctionCompiler.edgeSignal (endpoints R) {e | incidence e} x <;>
    cases b : LeafOrElimination.edgeSignal (splitEdges R) x <;> simp_all

theorem realize_split (R : List (Set Edge × Set Edge))
    (common : ∀ Z : Set Vertex, (∀ e : Edge, incidence e → e.1 ∈ Z ∨ e.2 ∈ Z) →
      {e | incidence e} ∈ R.foldl CoverUnion4653.step (CoverUnion4653.start Z)) :
    ∃ gates i, LeafOrElimination.orCount gates = R.length ∧
      LeafOrElimination.wire (ConjunctionCompiler.ref (finiteSeed SplitVertex)) (finiteSeed SplitVertex).length
        gates i = LeafOrElimination.edgeSignal (splitEdges R) := by
  classical
  let projected := R.map (fun r => (r.1 ∩ {e | incidence e}, r.2 ∩ {e | incidence e}))
  have computesCover : ∀ x, (∀ e ∈ {e | incidence e}, ConjunctionCompiler.covered (endpoints R) x e) →
      {e | incidence e} ∈ projected.foldl ConjunctionCompiler.unionStep (ConjunctionCompiler.stars (endpoints R) x) := by
    intro x cover
    exact CoverUnion4653.split_cover_transport R common {v | x v = false} cover
  let vertex (v : SplitVertex) := (Fintype.equivFin SplitVertex v).val + 2
  have wireValid (v : SplitVertex) : vertex v < (finiteSeed SplitVertex).length := by
    rw [finite_seed_length]
    exact Nat.add_lt_add_right (Fintype.equivFin SplitVertex v).isLt 2
  have wireValue (v : SplitVertex) : ConjunctionCompiler.ref (finiteSeed SplitVertex) (vertex v) = fun x => x v := by
    simpa using finite_seed_ref SplitVertex (Fintype.equivFin SplitVertex v)
  have zeroValid : 0 < (finiteSeed SplitVertex).length := by rw [finite_seed_length]; omega
  have oneValid : 1 < (finiteSeed SplitVertex).length := by rw [finite_seed_length]; omega
  obtain ⟨gates, out, cost, _, computes⟩ := ConjunctionCompiler.compile_finite_cover_union (endpoints R)
    projected {e | incidence e} computesCover (finiteSeed SplitVertex) vertex wireValid wireValue
    0 zeroValid rfl 1 oneValid rfl
  have reverse := CompilerBridge.reverse_matches (finiteSeed SplitVertex) gates.reverse out
  rw [List.reverse_reverse] at reverse
  refine ⟨gates.reverse.map CompilerBridge.reverseGate, out, ?_, reverse.trans (computes.trans (split_signal R))⟩
  rw [CompilerBridge.reverse_cost, List.reverse_reverse, cost]
  simp [projected]

theorem acyclic_centers_lower_bound (R : List (Set Edge × Set Edge))
    (acyclic : ((graphOf originalEdges).induce (operandCenters R)).IsAcyclic)
    (common : ∀ Z : Set Vertex, (∀ e : Edge, incidence e → e.1 ∈ Z ∨ e.2 ∈ Z) →
      {e | incidence e} ∈ R.foldl CoverUnion4653.step (CoverUnion4653.start Z)) : 104 ≤ R.length := by
  obtain ⟨gates, i, cost, computes⟩ := realize_split R common
  have nonempty : (splitEdges R).Nonempty := Finset.card_pos.mp (by rw [split_card]; decide)
  have bound := forest_or_lower_bound (splitEdges R) (split_pairs R) (retained_acyclic R acyclic) nonempty
    (ConjunctionCompiler.ref (finiteSeed SplitVertex)) (finiteSeed SplitVertex).length
    (finite_seed_primitive SplitVertex) gates i computes
  rw [split_card, cost] at bound
  exact bound

theorem short_program_has_core (R : List (Set Edge × Set Edge)) (short : R.length < 104)
    (common : ∀ Z : Set Vertex, (∀ e : Edge, incidence e → e.1 ∈ Z ∨ e.2 ∈ Z) →
      {e | incidence e} ∈ R.foldl CoverUnion4653.step (CoverUnion4653.start Z)) :
    ∃ (core : Finset (Finset SplitVertex)) (gates : List LeafOrElimination.Gate)
      (input : ℕ → LeafOrElimination.Signal SplitVertex) (i : ℕ),
      core ⊆ splitEdges R ∧ (∀ e ∈ core, ∀ s ∈ e, s ∈ retained R) ∧
      ¬ (graphOf core).IsAcyclic ∧ LeafOrElimination.orCount gates + 1 < core.card ∧
      (∀ j < (finiteSeed SplitVertex).length, LeafOrElimination.Primitive (input j)) ∧
      LeafOrElimination.wire input (finiteSeed SplitVertex).length gates i = LeafOrElimination.edgeSignal core := by
  classical
  obtain ⟨gates, i, cost, computes⟩ := realize_split R common
  have nonempty : (splitEdges R).Nonempty := Finset.card_pos.mp (by rw [split_card]; decide)
  obtain ⟨core, k, sub, coreNonempty, count, trace, final⟩ := peel_until_core (splitEdges R) nonempty
  obtain ⟨Q, input, costs, sources, output⟩ := LeafOrElimination.peel_to_core trace (split_pairs R)
    (ConjunctionCompiler.ref (finiteSeed SplitVertex)) (finiteSeed SplitVertex).length
    (finite_seed_primitive SplitVertex) gates i computes
  rw [split_card] at count
  have saving : LeafOrElimination.orCount Q + 1 < core.card := by omega
  have noLeaf := final.resolve_left (by omega)
  refine ⟨core, Q, input, i, sub, ?_, ?_, saving, sources, output⟩
  · intro e he s hs
    by_contra off
    exact noLeaf ⟨s, e, ⟨he, hs⟩, fun f hf => split_off_unique R s off (sub hf.1) (sub he) hf.2 hs⟩
  · intro acyclic
    exact noLeaf (forest_has_leaf core (fun e he => split_pairs R e (sub he)) acyclic coreNonempty)

end PG4

end ForestCase
