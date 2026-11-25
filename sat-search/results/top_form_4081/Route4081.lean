import PEqualNP.Outside.L_meta_7467

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
  PEqualNP.Outside.L_meta_7467

namespace Route4081

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

theorem uncoveredAcceptance (least : IsLeastAO G C) {u v : Fin n}
    (uncovered : s(u,v) ∈ Ustar G C) :
    (∃ a ∈ centreless G C, gateVal n C a (pairInput u v) = true) ∨
    (∃ a ∈ tops G C, ∃ b : Fin 2, ∃ m ∈ mixing G C,
      gateVal n C a (pairInput u v) = true ∧
      OrReaches n C (opnd C a b) m ∧ (orIn n C (n+m)).Nonempty ∧
      gateVal n C m (pairInput u v) = true) := by
  classical
  have adj : G.Adj u v := by simpa using (Finset.mem_sdiff.mp uncovered).1
  obtain ⟨a, ha, on⟩ := acceptedTop least adj
  by_cases hCentreless : a ∈ centreless G C
  · exact .inl ⟨a, hCentreless, on⟩
  have supported (b : Fin 2) : (side (n := n) C a b).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro empty
    apply hCentreless
    apply Finset.mem_filter.mpr
    fin_cases b
    · exact ⟨ha, .inl empty⟩
    · exact ⟨ha, .inr empty⟩
  have missing : ∃ b : Fin 2, ∀ w ∈ side C a b, pairInput u v w = false := by
    by_contra! each
    obtain ⟨l, hl, lon⟩ := each 0
    obtain ⟨r, hr, ron⟩ := each 1
    have lr := topAdj least.1 ha hl hr
    have member : s(l,r) ∈ starEdges G C := by
      apply Finset.mem_biUnion.mpr
      exact ⟨a, ha, Finset.mem_image.mpr ⟨(l,r), Finset.mem_product.mpr ⟨hl,hr⟩, rfl⟩⟩
    apply (Finset.mem_sdiff.mp uncovered).2
    have lon' : pairInput u v l = true := by cases h : pairInput u v l <;> simp_all
    have ron' : pairInput u v r = true := by cases h : pairInput u v r <;> simp_all
    rcases (pairInput_true u v l).mp lon' with leq | leq <;>
      rcases (pairInput_true u v r).mp ron' with req | req <;> subst l <;> subst r
    · exact (G.irrefl lr).elim
    · exact member
    · exact Sym2.eq_swap ▸ member
    · exact (G.irrefl lr).elim
  obtain ⟨b, absent⟩ := missing
  obtain ⟨al, hand, _⟩ := topData ha
  have operandOn := (andValOperands least.1 al hand (pairInput u v)).mp on b
  obtain ⟨m, hm, path, raw, mOn⟩ :=
    mixingSource (G := G) least.1 (pairInput u v) _ (supported b) operandOn absent
  exact .inr ⟨a, ha, b, m, hm, on, path, raw, mOn⟩

theorem oneMixerPins (least : IsLeastAO G C) (hc : centreless G C = ∅)
    {m : ℕ} (unique : ∀ j ∈ mixing G C, j = m)
    {u v : Fin n} (edge : s(u,v) ∈ Ustar G C) :
    ∃ pin : Fin n, pin ∈ s(u,v) ∧ pin ∈ wmax G C m ∧
      ∀ w ∈ orIn n C (n+m), G.Adj w pin := by
  classical
  rcases uncoveredAcceptance least edge with ⟨a, ha, _⟩ | ⟨a, ha, b, j, hj, on, path, raw, _⟩
  · simp [hc] at ha
  have eq := unique j hj
  subst j
  have rawSide (w : Fin n) (hw : w ∈ orIn n C (n+m)) : w ∈ side C a b :=
    orInTrans (orReaches_reach m _ path).1 hw
  have pinOn : ∃ pin ∈ side C a (1-b), pairInput u v pin = true := by
    by_contra! absent
    have off (p : Fin n) (hp : p ∈ side C a (1-b)) : pairInput u v p = false := by
      cases h : pairInput u v p
      · rfl
      · exact (absent p hp h).elim
    obtain ⟨al, hand, _⟩ := topData ha
    have other := (andValOperands least.1 al hand (pairInput u v)).mp on (1-b)
    obtain ⟨k, hk, otherPath, _, _⟩ :=
      mixingSource (G := G) least.1 (pairInput u v) _
        (topNonempty hc ha (1-b)) other off
    have eq := unique k hk
    subst k
    obtain ⟨w, hw⟩ := raw
    exact G.irrefl (oppositeAdj least.1 ha (rawSide w hw)
      (orInTrans (orReaches_reach m _ otherPath).1 hw))
  obtain ⟨pin, hpin, onPin⟩ := pinOn
  refine ⟨pin, Sym2.mem_iff.mpr ((pairInput_true u v pin).mp onPin),
    oppositeSideWmax least.1 ha path hpin, ?_⟩
  exact fun w hw => oppositeAdj least.1 ha (rawSide w hw) hpin

theorem oneMixerWideSupport (least : IsLeastAO G C) (hc : centreless G C = ∅)
    (four : NoFourCycle G) {m d : ℕ} (degree : ∀ v, G.degree v ≤ d)
    (unique : ∀ j ∈ mixing G C, j = m) (wide : 1 < (orIn n C (n+m)).card) :
    (Ustar G C).card ≤ d := by
  classical
  obtain ⟨p, hp, q, hq, ne⟩ := Finset.one_lt_card.mp wide
  let common := Finset.univ.filter fun w => G.Adj p w ∧ G.Adj q w
  have atMostOne : common.card ≤ 1 := four p q ne
  have pins (e : Sym2 (Fin n)) (he : e ∈ Ustar G C) : ∃ v ∈ common, v ∈ e := by
    induction e using Sym2.ind with
    | _ u v =>
      obtain ⟨pin, belongs, _, adjacent⟩ := oneMixerPins least hc unique he
      exact ⟨pin, Finset.mem_filter.mpr ⟨Finset.mem_univ _, adjacent p hp, adjacent q hq⟩, belongs⟩
  by_cases h : common.Nonempty
  · obtain ⟨v, hv⟩ := h
    have subset : Ustar G C ⊆ G.incidenceFinset v := by
      intro e he
      obtain ⟨w, hw, wp⟩ := pins e he
      have eq : w = v := Finset.card_le_one.mp atMostOne w hw v hv
      rw [G.incidenceFinset_eq_filter]
      exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp he).1, eq ▸ wp⟩
    exact (Finset.card_le_card subset).trans (by simpa only [G.card_incidenceFinset_eq_degree] using degree v)
  · have empty : Ustar G C = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      obtain ⟨w, hw, _⟩ := pins e he
      exact h ⟨w, hw⟩
    simp [empty]

theorem noUncoveredWithoutExceptions (least : IsLeastAO G C)
    (hc : centreless G C = ∅) (ho : orN G C \ lam G C = ∅) : Ustar G C = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  induction e using Sym2.ind with
  | _ u v =>
    rcases uncoveredAcceptance least he with ⟨a, ha, _⟩ | ⟨_, _, _, m, hm, _⟩
    · simp [hc] at ha
    · have outside := mixingOutside hm
      simp [ho] at outside

theorem atMostFourUncovered (least : IsLeastAO G C) (many : 3 ≤ (junk G C).card)
    (few : (Ustar G C).card ≤ 4) :
    (Ustar G C).card ≤ 2 * (centreless G C).card + (junk G C).card +
      (orN G C \ lam G C).card := by
  by_contra! deficit
  have hc : (centreless G C).card = 0 := by omega
  have ho : (orN G C \ lam G C).card = 0 := by omega
  have empty := noUncoveredWithoutExceptions least (Finset.card_eq_zero.mp hc)
    (Finset.card_eq_zero.mp ho)
  simp [empty] at deficit

end Route4081

#print axioms Route4081.atMostFourUncovered
#print axioms Route4081.oneMixerWideSupport
