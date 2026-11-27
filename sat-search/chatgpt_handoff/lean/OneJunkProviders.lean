import Mathlib
import PEqualNP.Defs

open PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover

namespace ResearchVerification.OneJunk

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

def nbr (c : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun v => G.Adj c v

theorem mem_nbr (c v : Fin n) : v ∈ nbr G c ↔ G.Adj c v := by
  simp [nbr]

/-- Shared providers in distinct neighbourhoods overlap in at most one raw input. -/
theorem commonNbrCard (h : NoFourCycle G) {c d : Fin n} (hne : c ≠ d) :
    (nbr G c ∩ nbr G d).card ≤ 1 := by
  have he : nbr G c ∩ nbr G d =
      Finset.univ.filter (fun v => G.Adj c v ∧ G.Adj d v) := by
    ext v
    simp [nbr]
  rw [he]
  exact h c d hne

/-- A protected OR support either survives whole, or filters to at most one input. -/
theorem protectedFilter (h : NoFourCycle G) (R : Finset (Fin n))
    (c d : Fin n) (hR : R ⊆ nbr G d) :
    R ∩ nbr G c = R ∨ (R ∩ nbr G c).card ≤ 1 := by
  by_cases he : c = d
  · left
    subst d
    exact Finset.inter_eq_left.mpr hR
  · right
    have hs : R ∩ nbr G c ⊆ nbr G c ∩ nbr G d := by
      intro v hv
      exact Finset.mem_inter.mpr
        ⟨(Finset.mem_inter.mp hv).2, hR (Finset.mem_inter.mp hv).1⟩
    exact (Finset.card_le_card hs).trans (commonNbrCard G h he)

/-- A list of old OR-DAG support nodes, in reverse topological order.
    Only merge nodes consume exclusive gate units. Protected gates already
    exist and are left untouched. Raw inputs are available independently. -/
inductive ProviderPlan (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (base : Finset (Fin n) → Prop) : List (Finset (Fin n)) → ℕ → Prop
  | nil : ProviderPlan G base [] 0
  | raw {L k} (v : Fin n) :
      ProviderPlan G base L k → ProviderPlan G base ({v} :: L) k
  | keepShared {L k} (R : Finset (Fin n)) (d : Fin n) :
      base R → R ⊆ nbr G d →
      ProviderPlan G base L k → ProviderPlan G base (R :: L) k
  | merge {L k} (A B : Finset (Fin n)) :
      A ∈ L → B ∈ L → ProviderPlan G base L k →
      ProviderPlan G base ((A ∪ B) :: L) (k + 1)

/-- A support-level OR computation. A free node is an unchanged existing
    provider, a raw input, or temporary zero. A merge costs one binary OR.
    Both operands refer to previously available nodes, so sharing is retained. -/
inductive FilteredPlan (free : Finset (Fin n) → Prop) :
    List (Finset (Fin n)) → ℕ → Prop
  | nil : FilteredPlan free [] 0
  | reuse {L k} (R : Finset (Fin n)) :
      free R → FilteredPlan free L k → FilteredPlan free (R :: L) k
  | merge {L k} (A B : Finset (Fin n)) :
      A ∈ L → B ∈ L → FilteredPlan free L k →
      FilteredPlan free ((A ∪ B) :: L) (k + 1)

/-- Filter an entire shared support DAG without increasing its exclusive
    OR budget. This is a support-level theorem; a separate embedding into
    the concrete Circuit wire numbering and deletion of temporary zeros is needed. -/
theorem filterPlan (h : NoFourCycle G) (c : Fin n)
    (base : Finset (Fin n) → Prop) {L : List (Finset (Fin n))} {k : ℕ}
    (p : ProviderPlan G base L k) :
    FilteredPlan (fun R => base R ∨ R.card ≤ 1)
      (L.map fun R => R ∩ nbr G c) k := by
  induction p with
  | nil => exact FilteredPlan.nil
  | raw v _ ih =>
      apply FilteredPlan.reuse
      · right
        have hs : ({v} : Finset (Fin n)) ∩ nbr G c ⊆ {v} :=
          fun _ hv => (Finset.mem_inter.mp hv).1
        calc
          (({v} : Finset (Fin n)) ∩ nbr G c).card ≤ ({v} : Finset (Fin n)).card :=
            Finset.card_le_card hs
          _ = 1 := Finset.card_singleton v
      · exact ih
  | keepShared R d hb hr _ ih =>
      apply FilteredPlan.reuse
      · rcases protectedFilter G h R c d hr with he | hc
        · left
          change base (R ∩ nbr G c)
          rw [he]
          exact hb
        · exact Or.inr hc
      · exact ih
  | merge A B ha hb _ ih =>
      have he : (A ∪ B) ∩ nbr G c = (A ∩ nbr G c) ∪ (B ∩ nbr G c) := by
        ext v
        simp only [Finset.mem_inter, Finset.mem_union]
        tauto
      simp only [List.map_cons, he]
      exact FilteredPlan.merge _ _
        (List.mem_map.mpr ⟨A, ha, rfl⟩)
        (List.mem_map.mpr ⟨B, hb, rfl⟩) ih

/-- Set-valued semantics of an OR provider. -/
def Hits (S : Finset (Fin n)) (x : Fin n → Bool) : Prop :=
  ∃ v ∈ S, x v = true

def pairBits (a b : Fin n) (v : Fin n) : Bool :=
  decide (v = a ∨ v = b)

theorem edge_of_pair (a b : Fin n)
    (hf : graphFun G ∅ (pairBits a b) = true) : G.Adj a b := by
  have he : ∃ u v, G.Adj u v ∧
      pairBits a b u = true ∧ pairBits a b v = true := by
    simpa [graphFun] using hf
  obtain ⟨u, v, huv, hu, hv⟩ := he
  have hu' : u = a ∨ u = b := by simpa [pairBits] using hu
  have hv' : v = a ∨ v = b := by simpa [pairBits] using hv
  rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl
  · exact (G.ne_of_adj huv rfl).elim
  · exact huv
  · exact (G.adj_comm _ _).mp huv
  · exact (G.ne_of_adj huv rfl).elim

/-- Clean raw products have every cross pair in the graph. -/
theorem crossAdj (A B : Finset (Fin n))
    (h : ∀ x, Hits A x → Hits B x → graphFun G ∅ x = true)
    {a b : Fin n} (ha : a ∈ A) (hb : b ∈ B) : G.Adj a b := by
  apply edge_of_pair G a b
  exact h _ ⟨a, ha, by simp [pairBits]⟩ ⟨b, hb, by simp [pairBits]⟩

/-- A vertex exposed by a cleaner in A is adjacent to every vertex of B. -/
theorem exposedCentre (A B C : Finset (Fin n))
    (h : ∀ x, Hits A x → Hits B x → Hits C x → graphFun G ∅ x = true)
    {a b : Fin n} (ha : a ∈ A) (hc : a ∈ C) (hb : b ∈ B) :
    G.Adj a b := by
  apply edge_of_pair G a b
  exact h _ ⟨a, ha, by simp [pairBits]⟩ ⟨b, hb, by simp [pairBits]⟩
    ⟨a, hc, by simp [pairBits]⟩

/-- Overlap vertices force every cleaner into their neighbourhood. -/
theorem overlapCleaner (A B C : Finset (Fin n))
    (h : ∀ x, Hits A x → Hits B x → Hits C x → graphFun G ∅ x = true)
    {a c : Fin n} (ha : a ∈ A) (hb : a ∈ B) (hc : c ∈ C) :
    G.Adj a c := by
  apply edge_of_pair G a c
  exact h _ ⟨a, ha, by simp [pairBits]⟩ ⟨a, hb, by simp [pairBits]⟩
    ⟨c, hc, by simp [pairBits]⟩

/-- At most one common neighbour of two distinct vertices, expressed as
    a reusable support bound. -/
theorem commonSupport (h : NoFourCycle G) (S : Finset (Fin n))
    {a b : Fin n} (hab : a ≠ b)
    (ha : ∀ v ∈ S, G.Adj a v) (hb : ∀ v ∈ S, G.Adj b v) :
    S.card ≤ 1 := by
  have hs : S ⊆ nbr G a ∩ nbr G b := by
    intro v hv
    exact Finset.mem_inter.mpr
      ⟨(mem_nbr G a v).mpr (ha v hv), (mem_nbr G b v).mpr (hb v hv)⟩
  exact (Finset.card_le_card hs).trans (commonNbrCard G h hab)

/-- The two-neighbour intersection case forces the cleaner support to have
    cardinality at most one. -/
theorem twoOverlapCleaner (h4 : NoFourCycle G) (A B C : Finset (Fin n))
    (h : ∀ x, Hits A x → Hits B x → Hits C x → graphFun G ∅ x = true)
    {a b : Fin n} (hne : a ≠ b) (ha : a ∈ A) (haB : a ∈ B)
    (hb : b ∈ A) (hbB : b ∈ B) : C.card ≤ 1 := by
  apply commonSupport G h4 C hne
  · intro v hv
    exact overlapCleaner G A B C h ha haB hv
  · intro v hv
    exact overlapCleaner G A B C h hb hbB hv

#print axioms protectedFilter
#print axioms filterPlan
#print axioms crossAdj
#print axioms exposedCentre
#print axioms twoOverlapCleaner

end ResearchVerification.OneJunk
