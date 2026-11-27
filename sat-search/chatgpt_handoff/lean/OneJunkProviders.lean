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


namespace SupportCompiler

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Pinned, previously checked wire evaluation helpers from L_meta_2668,
-- upstream PR #4874 (see attribution in OneJunkErase.lean).
def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt2 (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt2 gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt2 gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt2 _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

lemma opMono_eq : OpMono Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

lemma opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [ite_eq_right hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [ite_eq_left hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h'; exact ⟨hlt, h'⟩
    · rw [ite_eq_right hlt] at h'; cases h'
  · intro h i hi
    rw [ite_eq_left (h i hi).1]; exact (h i hi).2

lemma val_prefix {n : ℕ} {C D : Circuit} {x : List Bool} (hx : x.length = n) {m : ℕ}
    (hmC : m ≤ C.gates.length) (hmD : m ≤ D.gates.length)
    (hg : ∀ k < m, gateAt D k = gateAt C k) : ∀ u, u < n + m → val D x u = val C x u := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu
    by_cases hun : u < n
    · rw [val_input hx hun, val_input hx hun]
    · obtain ⟨k, rfl⟩ : ∃ k, u = n + k := ⟨u - n, by omega⟩
      have hk : k < m := by omega
      rw [val_gate hx (by omega), val_gate hx (by omega), hg k hk]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < n + k
      · rw [ite_eq_left hi, ite_eq_left hi]; exact ih i hi (by omega)
      · rw [ite_eq_right hi, ite_eq_right hi]


/-- An extension keeps the original gates and may append new ones. -/
def Extends (C D : Circuit) : Prop :=
  C.gates.length ≤ D.gates.length ∧
    ∀ j < C.gates.length, gateAt D j = gateAt C j

lemma extendsRefl (C : Circuit) : Extends C C :=
  ⟨le_rfl, fun _ _ => rfl⟩

lemma extendsTrans {C D E : Circuit} (h : Extends C D) (h' : Extends D E) :
    Extends C E := by
  refine ⟨h.1.trans h'.1,?_⟩
  intro j hj
  rw [h'.2 j (lt_of_lt_of_le hj h.1),h.2 j hj]

/-- Empty supports are a compile-time marker, not a real constant
    gate. Every nonempty support has a real earlier wire. -/
def Available {n : ℕ} (C : Circuit) (S : Finset (Fin n)) : Prop :=
  S = ∅ ∨ ∃ w < n + C.gates.length,
    ∀ x : Fin n → Bool, val C (List.ofFn x) w = true ↔ Hits S x

lemma availableExtends {n : ℕ} {C D : Circuit} (he : Extends C D)
    {S : Finset (Fin n)} (hS : Available C S) : Available D S := by
  rcases hS with heS | ⟨w,hw,hv⟩
  · exact Or.inl heS
  · refine Or.inr ⟨w,by have := he.1; omega,?_⟩
    intro x
    rw [val_prefix (n := n) (C := C) (D := D) (x := List.ofFn x)
      (by simp) le_rfl he.1 he.2 w hw]
    exact hv x

lemma availableSmall {n : ℕ} (C : Circuit) (S : Finset (Fin n))
    (hc : S.card ≤ 1) : Available C S := by
  by_cases h0 : S = ∅
  · exact Or.inl h0
  · obtain ⟨v,hv⟩ := Finset.nonempty_iff_ne_empty.mpr h0
    have hsub : ({v} : Finset (Fin n)) ⊆ S := Finset.singleton_subset_iff.mpr hv
    have hc' : S.card ≤ ({v} : Finset (Fin n)).card := by simpa using hc
    have he : ({v} : Finset (Fin n)) = S := Finset.eq_of_subset_of_card_le hsub hc'
    rw [← he]
    refine Or.inr ⟨v.val,by have := v.isLt; omega,?_⟩
    intro x
    rw [val_input (n := n) (by simp) v.isLt]
    simp [Hits,List.getD_eq_getElem?_getD,v.isLt]

def appendOr (C : Circuit) (a b : ℕ) : Circuit :=
  ⟨C.gates ++ [⟨GateOp.or,[a,b]⟩], C.output⟩

lemma appendOrLength (C : Circuit) (a b : ℕ) :
    (appendOr C a b).gates.length = C.gates.length + 1 := by
  simp [appendOr]

lemma appendOrOld {C : Circuit} {a b j : ℕ} (hj : j < C.gates.length) :
    gateAt (appendOr C a b) j = gateAt C j := by
  have hj' : j < (appendOr C a b).gates.length := by
    rw [appendOrLength]; omega
  rw [gateAt_eq hj',gateAt_eq hj]
  exact List.getElem_append_left hj

lemma appendOrNew (C : Circuit) (a b : ℕ) :
    gateAt (appendOr C a b) C.gates.length = ⟨GateOp.or,[a,b]⟩ := by
  have hj : C.gates.length < (appendOr C a b).gates.length := by
    rw [appendOrLength]; omega
  rw [gateAt_eq hj]
  simp [appendOr,List.getElem_append_right (le_refl C.gates.length)]

lemma appendOrExtends (C : Circuit) (a b : ℕ) : Extends C (appendOr C a b) := by
  refine ⟨?_,?_⟩
  · rw [appendOrLength]; omega
  · intro j hj
    exact appendOrOld hj

lemma appendOrAO {n : ℕ} {C : Circuit} (h : IsAO2 n C)
    {a b : ℕ} (ha : a < n + C.gates.length) (hb : b < n + C.gates.length) :
    IsAO2 n (appendOr C a b) := by
  refine ⟨?_,?_,?_⟩
  · intro g hg
    simp only [appendOr,List.mem_append,List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact h.1 _ hg
    · exact Or.inr rfl
  · intro j hj w hw
    by_cases hlt : j < C.gates.length
    · rw [appendOrOld hlt] at hw
      exact h.2.1 j hlt w hw
    · rw [appendOrLength] at hj
      have he : j = C.gates.length := by omega
      subst j
      rw [appendOrNew] at hw
      have hp : w = a ∨ w = b := by simpa using hw
      rcases hp with rfl | rfl
      · exact ha
      · exact hb
  · intro g hg
    simp only [appendOr,List.mem_append,List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact h.2.2 _ hg
    · rfl

/-- Merge actual nonempty provider wires with a single gate, or alias
    an existing support for free when either support is empty. -/
lemma availableUnion {n : ℕ} {C : Circuit} (h : IsAO2 n C)
    (A B : Finset (Fin n)) (hA : Available C A) (hB : Available C B) :
    ∃ D, IsAO2 n D ∧ Extends C D ∧ D.size ≤ C.size + 1 ∧ Available D (A ∪ B) := by
  rcases hA with heA | ⟨a,ha,hav⟩
  · subst A
    exact ⟨C,h,extendsRefl C,by omega,by simpa using hB⟩
  rcases hB with heB | ⟨b,hb,hbv⟩
  · subst B
    refine ⟨C,h,extendsRefl C,by omega,?_⟩
    rw [Finset.union_empty]
    exact Or.inr ⟨a,ha,hav⟩
  let D := appendOr C a b
  have he : Extends C D := appendOrExtends C a b
  have hD : IsAO2 n D := appendOrAO h ha hb
  have hsize : D.size = C.size + 1 := appendOrLength C a b
  refine ⟨D,hD,he,hsize.le,Or.inr ⟨n + C.gates.length,?_,?_⟩⟩
  · change n + C.gates.length < n + (appendOr C a b).gates.length
    rw [appendOrLength]
    omega
  · intro x
    have hj : C.gates.length < D.gates.length := by
      change C.gates.length < (appendOr C a b).gates.length
      rw [appendOrLength]
      omega
    have hgate : gateAt D C.gates.length = ⟨GateOp.or,[a,b]⟩ := appendOrNew C a b
    have hor : (gateAt D C.gates.length).op = GateOp.or := by rw [hgate]
    rw [val_or (n := n) (by simp) hj hor,hgate]
    have hva : val D (List.ofFn x) a = val C (List.ofFn x) a :=
      val_prefix (n := n) (by simp) le_rfl he.1 he.2 a ha
    have hvb : val D (List.ofFn x) b = val C (List.ofFn x) b :=
      val_prefix (n := n) (by simp) le_rfl he.1 he.2 b hb
    constructor
    · rintro ⟨w,hw,_,hval⟩
      have hp : w = a ∨ w = b := by simpa using hw
      rcases hp with rfl | rfl
      · rw [hva] at hval
        obtain ⟨v,hv,hx⟩ := (hav x).mp hval
        exact ⟨v,Finset.mem_union.mpr (Or.inl hv),hx⟩
      · rw [hvb] at hval
        obtain ⟨v,hv,hx⟩ := (hbv x).mp hval
        exact ⟨v,Finset.mem_union.mpr (Or.inr hv),hx⟩
    · rintro ⟨v,hv,hx⟩
      rcases Finset.mem_union.mp hv with hv | hv
      · exact ⟨a,by simp,ha,hva.trans ((hav x).mpr ⟨v,hv,hx⟩)⟩
      · exact ⟨b,by simp,hb,hvb.trans ((hbv x).mpr ⟨v,hv,hx⟩)⟩

/-- Compile the abstract shared-provider plan to a concrete exact AO2
    extension. The cost bound counts actual appended gates, and every
    existing base wire is preserved. No false constant is ever emitted. -/
theorem compileFilteredPlan {n : ℕ} (C : Circuit) (h : IsAO2 n C)
    (base : Finset (Fin n) → Prop)
    (hbase : ∀ R, base R → Available C R)
    {L : List (Finset (Fin n))} {k : ℕ}
    (p : FilteredPlan (fun R => base R ∨ R.card ≤ 1) L k) :
    ∃ D, IsAO2 n D ∧ Extends C D ∧ D.size ≤ C.size + k ∧
      ∀ R ∈ L, Available D R := by
  induction p with
  | nil =>
    refine ⟨C,h,extendsRefl C,by omega,?_⟩
    intro R hR
    simp at hR
  | reuse R hfree _ ih =>
    obtain ⟨D,hD,he,hsize,havail⟩ := ih
    refine ⟨D,hD,he,hsize,?_⟩
    intro S hS
    rcases List.mem_cons.mp hS with rfl | hm
    · rcases hfree with hb | hc
      · exact availableExtends he (hbase S hb)
      · exact availableSmall D S hc
    · exact havail S hm
  | merge A B ha hb _ ih =>
    obtain ⟨D,hD,he,hsize,havail⟩ := ih
    obtain ⟨E,hE,he',hsize',hAB⟩ := availableUnion hD A B (havail A ha) (havail B hb)
    refine ⟨E,hE,extendsTrans he he',by omega,?_⟩
    intro R hR
    rcases List.mem_cons.mp hR with rfl | hR
    · exact hAB
    · exact availableExtends he' (havail R hR)

#print axioms compileFilteredPlan

end SupportCompiler
end ResearchVerification.OneJunk
