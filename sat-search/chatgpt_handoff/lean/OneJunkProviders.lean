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


-- Strict shared-provider trimming. Drop contains precisely vertices
-- whose star edges can safely be covered elsewhere (or a superset of
-- them justified by the caller). No assumption of tree unfolding.

/-- The replacement support retains every vertex not authorized to
    be lost, has no new vertices, and omits the distinguished centre. -/
def TrimRel (a : Fin n) (Drop R T : Finset (Fin n)) : Prop :=
  T ⊆ R ∧ a ∉ T ∧ ∀ v ∈ R, v ∉ Drop → v ∈ T

lemma trimKeep (a : Fin n) (Drop R : Finset (Fin n)) (ha : a ∉ R) :
    TrimRel a Drop R R := ⟨fun _ h => h, ha, fun _ h _ => h⟩

lemma trimDrop (a : Fin n) (Drop R : Finset (Fin n)) (hR : R ⊆ Drop) :
    TrimRel a Drop R ∅ := by
  refine ⟨Finset.empty_subset _, by simp, ?_⟩
  intro v hv hn
  exact (hn (hR hv)).elim

lemma trimUnion (a : Fin n) (Drop A B X Y : Finset (Fin n))
    (hx : TrimRel a Drop A X) (hy : TrimRel a Drop B Y) :
    TrimRel a Drop (A ∪ B) (X ∪ Y) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    rcases Finset.mem_union.mp hv with h | h
    · exact Finset.mem_union.mpr (Or.inl (hx.1 h))
    · exact Finset.mem_union.mpr (Or.inr (hy.1 h))
  · intro hv
    rcases Finset.mem_union.mp hv with h | h
    · exact hx.2.1 h
    · exact hy.2.1 h
  · intro v hv hn
    rcases Finset.mem_union.mp hv with h | h
    · exact Finset.mem_union.mpr (Or.inl (hx.2.2 v h hn))
    · exact Finset.mem_union.mpr (Or.inr (hy.2.2 v h hn))

/-- All original support nodes have a suitable replacement. If no
    exclusive OR has yet been saved, every old support containing a
    has an available zero replacement and lies in Drop. -/
def TrimState (a : Fin n) (Drop : Finset (Fin n))
    (base : Finset (Fin n) → Prop) (L : List (Finset (Fin n))) (k : ℕ) : Prop :=
  ∃ M l, FilteredPlan (fun R => base R ∨ R.card ≤ 1) M l ∧ l ≤ k ∧
    (∀ R ∈ L, ∃ T ∈ M, TrimRel a Drop R T) ∧
    (l = k → ∀ R ∈ L, a ∈ R → R ⊆ Drop ∧ (∅ : Finset (Fin n)) ∈ M)

lemma trimStateReuse (a : Fin n) (Drop : Finset (Fin n))
    (base : Finset (Fin n) → Prop) {L : List (Finset (Fin n))} {k : ℕ}
    (st : TrimState a Drop base L k) (R T : Finset (Fin n))
    (hfree : base T ∨ T.card ≤ 1) (htrim : TrimRel a Drop R T)
    (hzero : a ∈ R → R ⊆ Drop ∧ T = ∅) :
    TrimState a Drop base (R :: L) k := by
  obtain ⟨M,l,hM,hl,hrel,hz⟩ := st
  refine ⟨T :: M,l,FilteredPlan.reuse T hfree hM,hl,?_,?_⟩
  · intro S hS
    rcases List.mem_cons.mp hS with rfl | hS
    · exact ⟨T,List.mem_cons_self, htrim⟩
    · obtain ⟨U,hU,htr⟩ := hrel S hS
      exact ⟨U,List.mem_cons_of_mem _ hU,htr⟩
  · intro he S hS ha
    rcases List.mem_cons.mp hS with rfl | hS
    · obtain ⟨hd,heT⟩ := hzero ha
      exact ⟨hd,by rw [heT]; exact List.mem_cons_self⟩
    · obtain ⟨hd,hm⟩ := hz he S hS ha
      exact ⟨hd,List.mem_cons_of_mem _ hm⟩

lemma trimStateMerge (a : Fin n) (Drop : Finset (Fin n))
    (base : Finset (Fin n) → Prop) {L : List (Finset (Fin n))} {k : ℕ}
    (st : TrimState a Drop base L k) (A B : Finset (Fin n))
    (ha : A ∈ L) (hb : B ∈ L) :
    TrimState a Drop base ((A ∪ B) :: L) (k+1) := by
  obtain ⟨M,l,hM,hl,hrel,hz⟩ := st
  obtain ⟨X,hX,htX⟩ := hrel A ha
  obtain ⟨Y,hY,htY⟩ := hrel B hb
  by_cases hsave : l = k ∧ a ∈ A ∪ B
  · obtain ⟨he,hm⟩ := hsave
    have hnew : ∃ T ∈ M, TrimRel a Drop (A ∪ B) T := by
      rcases Finset.mem_union.mp hm with ha' | hb'
      · obtain ⟨hAd,_⟩ := hz he A ha ha'
        refine ⟨Y,hY,?_⟩
        simpa only [Finset.empty_union] using
          trimUnion a Drop A B ∅ Y (trimDrop a Drop A hAd) htY
      · obtain ⟨hBd,_⟩ := hz he B hb hb'
        refine ⟨X,hX,?_⟩
        simpa only [Finset.union_empty] using
          trimUnion a Drop A B X ∅ htX (trimDrop a Drop B hBd)
    refine ⟨M,l,hM,by omega,?_,?_⟩
    · intro R hR
      rcases List.mem_cons.mp hR with rfl | hR
      · exact hnew
      · exact hrel R hR
    · intro he'
      omega
  · refine ⟨(X ∪ Y) :: M,l+1,FilteredPlan.merge X Y hX hY hM,by omega,?_,?_⟩
    · intro R hR
      rcases List.mem_cons.mp hR with rfl | hR
      · exact ⟨X ∪ Y,List.mem_cons_self,trimUnion a Drop A B X Y htX htY⟩
      · obtain ⟨T,hT,ht⟩ := hrel R hR
        exact ⟨T,List.mem_cons_of_mem _ hT,ht⟩
    · intro he R hR hRa
      have he' : l = k := by omega
      rcases List.mem_cons.mp hR with rfl | hR
      · exact (hsave ⟨he',hRa⟩).elim
      · obtain ⟨hd,hm⟩ := hz he' R hR hRa
        exact ⟨hd,List.mem_cons_of_mem _ hm⟩

/-- Trim a shared plan without increasing its exclusive OR count.
    Every shared node containing a may be discarded from the new
    provider only when all its vertices lie in the authorized Drop set. -/
theorem trimPlan (a : Fin n) (Drop : Finset (Fin n)) (haD : a ∈ Drop)
    (base : Finset (Fin n) → Prop)
    (hdrop : ∀ R, base R → a ∈ R → R ⊆ Drop)
    {L : List (Finset (Fin n))} {k : ℕ} (p : ProviderPlan G base L k) :
    TrimState a Drop base L k := by
  induction p with
  | nil =>
    refine ⟨[],0,FilteredPlan.nil,le_rfl,?_,?_⟩
    · intro R hR
      simp at hR
    · intro _ R hR
      simp at hR
  | raw v _ ih =>
    by_cases he : v = a
    · subst v
      have hsub : ({a} : Finset (Fin n)) ⊆ Drop := by simpa using haD
      exact trimStateReuse a Drop base ih {a} ∅ (Or.inr (by simp))
        (trimDrop a Drop {a} hsub) (fun _ => ⟨hsub,rfl⟩)
    · have hn : a ∉ ({v} : Finset (Fin n)) := by
        simpa using Ne.symm he
      exact trimStateReuse a Drop base ih {v} {v} (Or.inr (by simp))
        (trimKeep a Drop {v} hn) (fun h => (hn h).elim)
  | keepShared R d hbase _ _ ih =>
    by_cases ha : a ∈ R
    · have hd := hdrop R hbase ha
      exact trimStateReuse a Drop base ih R ∅ (Or.inr (by simp))
        (trimDrop a Drop R hd) (fun _ => ⟨hd,rfl⟩)
    · exact trimStateReuse a Drop base ih R R (Or.inl hbase)
        (trimKeep a Drop R ha) (fun h => (ha h).elim)
  | merge A B ha hb _ ih =>
    exact trimStateMerge a Drop base ih A B ha hb

/-- The strict second filter at an exclusive OR root. The original
    plan including this root costs k+1, but the rebuilt support needs
    at most k exclusive merges. This is not merely a nonincrease. -/
theorem trimExclusiveRoot (a : Fin n) (Drop : Finset (Fin n)) (haD : a ∈ Drop)
    (base : Finset (Fin n) → Prop)
    (hdrop : ∀ R, base R → a ∈ R → R ⊆ Drop)
    {L : List (Finset (Fin n))} {k : ℕ} (p : ProviderPlan G base L k)
    (A B : Finset (Fin n)) (ha : A ∈ L) (hb : B ∈ L) (hroot : a ∈ A ∪ B) :
    ∃ M l T, FilteredPlan (fun R => base R ∨ R.card ≤ 1) M l ∧ l ≤ k ∧
      T ∈ M ∧ TrimRel a Drop (A ∪ B) T := by
  obtain ⟨M,l,hM,hl,hrel,hz⟩ := trimPlan G a Drop haD base hdrop p
  obtain ⟨X,hX,htX⟩ := hrel A ha
  obtain ⟨Y,hY,htY⟩ := hrel B hb
  by_cases he : l = k
  · rcases Finset.mem_union.mp hroot with ha' | hb'
    · obtain ⟨hAd,_⟩ := hz he A ha ha'
      refine ⟨M,l,Y,hM,hl,hY,?_⟩
      simpa only [Finset.empty_union] using
        trimUnion a Drop A B ∅ Y (trimDrop a Drop A hAd) htY
    · obtain ⟨hBd,_⟩ := hz he B hb hb'
      refine ⟨M,l,X,hM,hl,hX,?_⟩
      simpa only [Finset.union_empty] using
        trimUnion a Drop A B X ∅ htX (trimDrop a Drop B hBd)
  · refine ⟨(X ∪ Y)::M,l+1,X ∪ Y,FilteredPlan.merge X Y hX hY hM,
      by omega,List.mem_cons_self,?_⟩
    exact trimUnion a Drop A B X Y htX htY

#print axioms trimPlan
#print axioms trimExclusiveRoot

end ResearchVerification.OneJunk
