import OneJunkErase
import PEqualNP.Outside.L_meta_4745
import PEqualNP.Outside.L_meta_4746
import PEqualNP.Outside.L_meta_4747

namespace ResearchVerification.OneJunkErase

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.Core
open PEqualNP.CleanedNonEdge (OrReaches wireVal)
open PEqualNP.EdgeOwnership (gateVal pairInput)
open PEqualNP.SplitCount (unitInput)
open PEqualNP.MetaComplexity.LowerPart (opnd_lt reach_gate reach_le OneDirty)
open PEqualNP.Outside.L_meta_4745 (PZ)

private theorem fromLeastOneJunk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    {r : ℕ} (hJ : junk G C = {r}) : OneDirty G C r := by
  obtain ⟨hr, hand, hdirty⟩ := junkMember G C hJ
  refine ⟨h.1, h.2.1, hl, ?_, allLive G C h, hr, hand, hdirty, ?_⟩
  · intro j hj ho w hw
    exact noCleanAndOperand G C h j w hj hw ho
  · intro j hj ho hjr
    by_contra hnd
    exact hjr (uniqueDirtyAnd G C hJ hj hnd ho)

private theorem rawFormJunkReaches {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    {r w : ℕ} (hJ : junk G C = {r}) (hw : w < n + C.gates.length)
    (hd : ¬ CleanWire G C w) {S : Finset (Fin n)} (hS : RawForm C r w S true) :
    OrReaches n C w r := by
  obtain ⟨V, hV, hfill⟩ := existsEvalExceptWithJunk C h.1 r (fun _ => true)
  let zero : Fin n → Bool := fun _ => false
  have carries : ∀ i < n + C.gates.length, ¬ CleanWire G C i →
      V zero i = true → OrReaches n C i r := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi hdirty hv
      by_cases hin : i < n
      · have hraw := hV.1 zero ⟨i, hin⟩
        rw [hraw] at hv
        cases hv
      · obtain ⟨j, rfl⟩ : ∃ j, i = n + j := ⟨i - n, by omega⟩
        have hj : j < C.gates.length := by omega
        apply (reach_gate C h.1 j r hj).mpr
        by_cases hjr : j = r
        · exact Or.inl hjr.symm
        rcases h.1.1 _ (gateAt_mem hj) with hand | hor
        · exact (hjr (uniqueDirtyAnd G C hJ hj hdirty hand)).elim
        · obtain ⟨p, q, hpq⟩ := twoOperands h.1 hj
          have propagate (u : ℕ) (hu : u ∈ (gateAt C j).inputs) (hv : V zero u = true) :
              OrReaches n C u r := by
            have hup := h.1.2.1 j hj u hu
            exact ih u hup (by omega) (fun hc => hdirty (cleanWireReader G C h hl hj hu hc).2) hv
          obtain ⟨u, hu, hv⟩ := (evalExcept_or hV hj hjr hor zero).mp hv
          have hreach := propagate u hu hv
          have hside : u = p ∨ u = q := by simpa [hpq] using hu
          refine Or.inr ⟨hor, ?_⟩
          rcases hside with rfl | rfl
          · refine ⟨0, ?_⟩
            simpa [opnd, hpq] using hreach
          · refine ⟨1, ?_⟩
            simpa [opnd, hpq] using hreach
  exact carries w hw hd ((hS.2 V hV zero).mpr (Or.inr ⟨rfl, hfill zero⟩))

private theorem rawMemberAtUnit {n : ℕ} {C : Circuit} {r w : ℕ}
    (h : IsAO2 n C) {S : Finset (Fin n)} {b : Bool} (hS : RawForm C r w S b)
    {z : Fin n} (hz : z ∈ S) : wireVal n C w (unitInput z) = true :=
  (hS.2 _ (originalEvalExcept h r) (unitInput z)).mpr
    (Or.inl ⟨z, hz, by simp [unitInput]⟩)

private theorem rawFalseAtUnit {n : ℕ} {C : Circuit} {r w : ℕ}
    (h : IsAO2 n C) {S : Finset (Fin n)} (hS : RawForm C r w S false) (z : Fin n) :
    wireVal n C w (unitInput z) = true ↔ z ∈ S := by
  constructor
  · intro hz
    rcases (hS.2 _ (originalEvalExcept h r) (unitInput z)).mp hz with ⟨v, hv, hunit⟩ | hflag
    · have hvz : v = z := by simpa [unitInput] using hunit
      exact hvz ▸ hv
    · cases hflag.1
  · exact rawMemberAtUnit h hS

private theorem junkAtUnit {n : ℕ} {C : Circuit} (h : IsAO2 n C)
    {r a b : ℕ} (hr : r < C.gates.length) (hand : (gateAt C r).op = GateOp.and)
    (hab : (gateAt C r).inputs = [a, b])
    {A B : Finset (Fin n)} (hA : RawForm C r a A false) (hB : RawForm C r b B false)
    (z : Fin n) : gateVal n C r (unitInput z) = true ↔ z ∈ A ∧ z ∈ B := by
  have hval := evalExcept_and (originalEvalExcept h C.gates.length)
    hr (Nat.ne_of_lt hr) hand hab (unitInput z)
  change gateVal n C r (unitInput z) = true ↔
    wireVal n C a (unitInput z) = true ∧ wireVal n C b (unitInput z) = true at hval
  rwa [rawFalseAtUnit h hA, rawFalseAtUnit h hB] at hval

/-- Accepted upstream reductions handle exposed readers. The local bypass handles the
    remaining case once a true suspended-junk flag is translated to OR reachability. -/
theorem noSingletonOverlapWithUpstream {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C) (h4 : NoFourCycle G)
    (colour : Fin n → Bool) (hcolour : ∀ u v, G.Adj u v → colour u ≠ colour v)
    {r a b : ℕ} (hJ : junk G C = {r}) (hab : (gateAt C r).inputs = [a, b])
    {A B : Finset (Fin n)} (hA : RawForm C r a A false) (hB : RawForm C r b B false)
    {s : Fin n} (hsA : s ∈ A) (hsB : s ∈ B) (hshared : ∀ z ∈ A, z ∈ B → z = s) :
    False := by
  classical
  have H := fromLeastOneJunk G C h hl hJ
  have hunit (z : Fin n) : gateVal n C r (unitInput z) = true ↔ z = s := by
    rw [junkAtUnit H.ao H.hg H.gand hab hA hB]
    exact ⟨fun hz => hshared z hz.1 hz.2, fun hz => hz.symm ▸ ⟨hsA, hsB⟩⟩
  by_cases exposed : ∃ m, (m ∈ A ∨ m ∈ B) ∧
      ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧ PZ C r j m
  · obtain ⟨m, hm, hreader⟩ := exposed
    have hmroot : wireVal n C (opnd C r 0) (unitInput m) = true ∨
        wireVal n C (opnd C r 1) (unitInput m) = true := by
      rcases hm with hm | hm
      · exact Or.inl (by simpa [opnd, hab] using rawMemberAtUnit h.1 hA hm)
      · exact Or.inr (by simpa [opnd, hab] using rawMemberAtUnit h.1 hB hm)
    let paired := fun j z =>
      (OrReaches n C (opnd C j 0) r ∧ wireVal n C (opnd C j 1) (unitInput m) = true ∧
        wireVal n C (opnd C j 1) (unitInput z) = true) ∨
      (OrReaches n C (opnd C j 1) r ∧ wireVal n C (opnd C j 0) (unitInput m) = true ∧
        wireVal n C (opnd C j 0) (unitInput z) = true)
    have smaller : ∃ D : Circuit, IsAO2 n D ∧ D.size < C.size ∧
        circuitFun n D = graphFun G ∅ := by
      by_cases split : ∃ z ≠ m, ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧ paired j z
      · obtain ⟨z, hzm, hj⟩ := split
        exact PEqualNP.Outside.L_meta_4745 n G C colour r s m z hcolour h4 H.ao H.comp H.lift
          H.andLow H.cone H.hg H.gand H.dirty H.others hunit hmroot hzm hj
      · apply PEqualNP.Outside.L_meta_4746 n G C colour r s m hcolour h4 H.ao H.comp H.lift
          H.andLow H.cone H.hg H.gand H.dirty H.others hunit hmroot hreader
        intro j hj ho z hz
        by_contra hzm
        exact split ⟨z, hzm, j, hj, ho, hz⟩
    obtain ⟨D, hD, hsmaller, hfun⟩ := smaller
    exact (Nat.not_lt_of_ge (h.2.2 D hD hfun)) hsmaller
  · apply noSingleOverlapNoExposure G C h hl hJ hab A B hA hB s hsA hsB hshared
    intro j hj ho _ p q S T f g hpq hP hQ
    have hp : p ∈ (gateAt C j).inputs := by simp [hpq]
    have hq : q ∈ (gateAt C j).inputs := by simp [hpq]
    have hbound (w : ℕ) (hw : w ∈ (gateAt C j).inputs) : w < n + C.gates.length :=
      (h.1.2.1 j hj w hw).trans (Nat.add_lt_add_left hj n)
    have exclude (z : Fin n) (hz : PZ C r j z) : z ∉ A ∧ z ∉ B :=
      ⟨fun hzA => exposed ⟨z, Or.inl hzA, j, hj, ho, hz⟩,
        fun hzB => exposed ⟨z, Or.inr hzB, j, hj, ho, hz⟩⟩
    constructor
    · rintro rfl z hz
      apply exclude
      have reach := rawFormJunkReaches G C h hl hJ (hbound p hp) (H.andLow j hj ho p hp) hP
      simpa [PZ, opnd, hpq] using
        (Or.inl ⟨reach, rawMemberAtUnit h.1 hQ hz⟩ :
          (OrReaches n C p r ∧ wireVal n C q (unitInput z) = true) ∨
          (OrReaches n C q r ∧ wireVal n C p (unitInput z) = true))
    · rintro rfl z hz
      apply exclude
      have reach := rawFormJunkReaches G C h hl hJ (hbound q hq) (H.andLow j hj ho q hq) hQ
      simpa [PZ, opnd, hpq] using
        (Or.inr ⟨reach, rawMemberAtUnit h.1 hP hz⟩ :
          (OrReaches n C p r ∧ wireVal n C q (unitInput z) = true) ∨
          (OrReaches n C q r ∧ wireVal n C p (unitInput z) = true))

/-- The dirty AND's two raw supports are disjoint in the minimum one-junk setting. -/
theorem oneJunkSupportsDisjoint {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C) (h4 : NoFourCycle G)
    (colour : Fin n → Bool) (hcolour : ∀ u v, G.Adj u v → colour u ≠ colour v)
    {r a b : ℕ} (hJ : junk G C = {r}) (hab : (gateAt C r).inputs = [a, b])
    {A B : Finset (Fin n)} (hA : RawForm C r a A false) (hB : RawForm C r b B false) :
    Disjoint A B := by
  classical
  refine Finset.disjoint_left.mpr ?_
  intro s hsA hsB
  by_cases second : ∃ z ∈ A, z ∈ B ∧ z ≠ s
  · obtain ⟨z, hzA, hzB, hzs⟩ := second
    exact noTwoOverlap G C h hl h4 hJ hab hA hB hsA hsB hzA hzB hzs.symm
  · apply noSingletonOverlapWithUpstream G C h hl h4 colour hcolour hJ hab hA hB hsA hsB
    intro z hzA hzB
    by_contra hzs
    exact second ⟨z, hzA, hzB, hzs⟩

/-- The hypotheses of the disjoint-support reductions hold on all unit inputs. -/
theorem oneJunkFalseOnUnit {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C) (h4 : NoFourCycle G)
    (colour : Fin n → Bool) (hcolour : ∀ u v, G.Adj u v → colour u ≠ colour v)
    {r : ℕ} (hJ : junk G C = {r}) (z : Fin n) : gateVal n C r (unitInput z) = false := by
  obtain ⟨a, b, A, B, hr, hand, hab, _, _, hA, hB, _⟩ := junkProduct G C h hl hJ
  have hd := oneJunkSupportsDisjoint G C h hl h4 colour hcolour hJ hab hA hB
  cases hz : gateVal n C r (unitInput z) with
  | false => rfl
  | true =>
    have hzAB := (junkAtUnit h.1 hr hand hab hA hB z).mp hz
    exact (Finset.disjoint_left.mp hd hzAB.1 hzAB.2).elim

/-- A remaining one-junk circuit must have a clean AND whose junk-carrying
    operand contributes on an edge input with a unit-active opposite operand. -/
theorem oneJunkHasEdgeReader {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C) (h4 : NoFourCycle G)
    (colour : Fin n → Bool) (hcolour : ∀ u v, G.Adj u v → colour u ≠ colour v)
    {r : ℕ} (hJ : junk G C = {r}) :
    ∃ j < C.gates.length, r < j ∧ (gateAt C j).op = GateOp.and ∧ BelowF G C j ∧
      ∃ u z, G.Adj u z ∧ PZ C r j z ∧ gateVal n C r (pairInput u z) = true := by
  classical
  have H := fromLeastOneJunk G C h hl hJ
  by_contra absent
  have noEdge (j : ℕ) (hj : j < C.gates.length) (ho : (gateAt C j).op = GateOp.and)
      (u z : Fin n) (hadj : G.Adj u z) (hex : PZ C r j z) :
      gateVal n C r (pairInput u z) = false := by
    cases hv : gateVal n C r (pairInput u z) with
    | false => rfl
    | true =>
      obtain ⟨side, hreach, _⟩ := (PEqualNP.Outside.L_meta_4745.pz_iff C r j z).mp hex
      have hprev := opnd_lt C H.ao j hj side
      have hb : opnd C j side < n + C.gates.length := hprev.trans (Nat.add_lt_add_left hj n)
      have hle := (reach_le C H.ao r _ hb hreach).1
      have hrj : r < j := by omega
      exact (absent ⟨j, hj, hrj, ho, H.others j hj ho hrj.ne.symm, u, z, hadj, hex, hv⟩).elim
  obtain ⟨D, hD, hsmaller, hfun⟩ := PEqualNP.Outside.L_meta_4747 n G C colour r hcolour h4
    H.ao H.comp H.lift H.andLow H.cone H.hg H.gand H.dirty H.others
    (oneJunkFalseOnUnit G C h hl h4 colour hcolour hJ) noEdge
  exact (Nat.not_lt_of_ge (h.2.2 D hD hfun)) hsmaller

#print axioms rawFormJunkReaches
#print axioms noSingletonOverlapWithUpstream
#print axioms oneJunkSupportsDisjoint
#print axioms oneJunkFalseOnUnit
#print axioms oneJunkHasEdgeReader

end ResearchVerification.OneJunkErase
