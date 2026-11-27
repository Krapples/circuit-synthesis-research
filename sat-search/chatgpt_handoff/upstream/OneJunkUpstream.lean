import OneJunkErase
import PEqualNP.Outside.L_meta_4712
import PEqualNP.Outside.L_meta_4743
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
open PEqualNP.MetaComplexity.FoldProg
  (Closed Sol Res srcAt opv kept wireVal_input isAO2_snoc wireVal_new wireVal_old
    srcOf srcOf_inr progOf isA)
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

private theorem junkAtPair {n : ℕ} {C : Circuit} (h : IsAO2 n C)
    {r a b : ℕ} (hr : r < C.gates.length) (hand : (gateAt C r).op = GateOp.and)
    (hab : (gateAt C r).inputs = [a, b])
    {A B : Finset (Fin n)} (hA : RawForm C r a A false) (hB : RawForm C r b B false)
    (u z : Fin n) : gateVal n C r (pairInput u z) = true ↔
      (u ∈ A ∨ z ∈ A) ∧ (u ∈ B ∨ z ∈ B) := by
  have pair_support (S : Finset (Fin n)) :
      (∃ v ∈ S, pairInput u z v = true) ↔ u ∈ S ∨ z ∈ S := by
    constructor
    · rintro ⟨v, hv, hpair⟩
      have eq : v = u ∨ v = z := by simpa [pairInput] using hpair
      rcases eq with rfl | rfl
      · exact Or.inl hv
      · exact Or.inr hv
    · rintro (hu | hz)
      · exact ⟨u, hu, by simp [pairInput]⟩
      · exact ⟨z, hz, by simp [pairInput]⟩
  have hV := originalEvalExcept h C.gates.length
  change val C (List.ofFn (pairInput u z)) (n + r) = true ↔ _
  rw [evalExcept_and hV hr (Nat.ne_of_lt hr) hand hab]
  rw [(hA.2 _ (originalEvalExcept h r) _), (hB.2 _ (originalEvalExcept h r) _)]
  simp only [Bool.false_eq_true, false_and, or_false, pair_support]

/-- The remaining one-junk case has two disjoint supports of size at least two,
    in opposite colour classes, and a reader exposing a vertex adjacent to all
    vertices of the opposite support. -/
theorem oneJunkLargeOppositeSupports {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C) (h4 : NoFourCycle G)
    (colour : Fin n → Bool) (hcolour : ∀ u v, G.Adj u v → colour u ≠ colour v)
    {r : ℕ} (hJ : junk G C = {r}) :
    ∃ a b : ℕ, ∃ A B : Finset (Fin n), ∃ c : Bool,
      (gateAt C r).inputs = [a, b] ∧ RawForm C r a A false ∧ RawForm C r b B false ∧
      Disjoint A B ∧ 1 < A.card ∧ 1 < B.card ∧
      (∀ v ∈ A, colour v = c) ∧ (∀ v ∈ B, colour v ≠ c) ∧
      ∃ z, ((z ∈ A ∧ ∀ v ∈ B, G.Adj v z) ∨ (z ∈ B ∧ ∀ v ∈ A, G.Adj v z)) ∧
        ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧ PZ C r j z := by
  classical
  have H := fromLeastOneJunk G C h hl hJ
  have hunit := oneJunkFalseOnUnit G C h hl h4 colour hcolour hJ
  obtain ⟨a, b, A, B, _, _, hab, _, _, hA, hB, hAn, hBn, _⟩ := junkProduct G C h hl hJ
  have hd := oneJunkSupportsDisjoint G C h hl h4 colour hcolour hJ hab hA hB
  have hpair := junkAtPair H.ao H.hg H.gand hab hA hB
  have unitA (v : Fin n) : wireVal n C (opnd C r 0) (unitInput v) = true ↔ v ∈ A := by
    simpa [opnd, hab] using rawFalseAtUnit H.ao hA v
  have unitB (v : Fin n) : wireVal n C (opnd C r 1) (unitInput v) = true ↔ v ∈ B := by
    simpa [opnd, hab] using rawFalseAtUnit H.ao hB v
  obtain ⟨j, hj, _, hjand, hjclean, u, z, huz, hex, hujunk⟩ :=
    oneJunkHasEdgeReader G C h hl h4 colour hcolour hJ
  obtain ⟨side, hreach, hopp⟩ := (PEqualNP.Outside.L_meta_4745.pz_iff C r j z).mp hex
  have hadj (v : Fin n) (hv : gateVal n C r (pairInput v z) = true) : G.Adj v z := by
    have hb := (opnd_lt C H.ao j hj side).trans (Nat.add_lt_add_left hj n)
    have hcarry := (reach_le C H.ao r _ hb hreach).2 _ hv
    have hother : wireVal n C (opnd C j (1 - side)) (pairInput v z) = true :=
      wire_monotone n C (ao_mono H.ao) _ _
        (fun t ht => by
          have eq : t = z := by simpa [unitInput] using ht
          simp [eq, pairInput]) _ hopp
    exact PEqualNP.Outside.L_meta_4745.pair_adj G v z
      (hjclean _ ((PEqualNP.Outside.L_meta_4745.val_and' C H.ao j hj hjand _ side).mpr
        ⟨hcarry, hother⟩))
  let Mono := fun S : Finset (Fin n) => ∀ v ∈ S, ∀ w ∈ S, colour v = colour w
  have oriented : (u ∈ A ∧ z ∈ B) ∨ (z ∈ A ∧ u ∈ B) := by
    rcases (hpair u z).mp hujunk with ⟨huA | hzA, huB | hzB⟩
    · exact (Finset.disjoint_left.mp hd huA huB).elim
    · exact Or.inl ⟨huA, hzB⟩
    · exact Or.inr ⟨hzA, huB⟩
    · exact (Finset.disjoint_left.mp hd hzA hzB).elim
  have centre : (z ∈ A ∧ ∀ v ∈ B, G.Adj v z) ∨ (z ∈ B ∧ ∀ v ∈ A, G.Adj v z) := by
    rcases oriented with ⟨_, hzB⟩ | ⟨hzA, _⟩
    · exact Or.inr ⟨hzB, fun v hv => hadj v ((hpair v z).mpr ⟨Or.inl hv, Or.inr hzB⟩)⟩
    · exact Or.inl ⟨hzA, fun v hv => hadj v ((hpair v z).mpr ⟨Or.inr hzA, Or.inl hv⟩)⟩
  have someMono : Mono A ∨ Mono B := by
    have sameOtherColour {x y c : Bool} (hx : x ≠ c) (hy : y ≠ c) : x = y := by
      cases x <;> cases y <;> cases c <;> simp_all
    rcases centre with ⟨_, hz⟩ | ⟨_, hz⟩
    · exact Or.inr (fun v hv w hw => sameOtherColour (hcolour v z (hz v hv)) (hcolour w z (hz w hw)))
    · exact Or.inl (fun v hv w hw => sameOtherColour (hcolour v z (hz v hv)) (hcolour w z (hz w hw)))
  have mixed {S : Finset (Fin n)} (hm : ¬ Mono S) :
      ∃ v ∈ S, ∃ w ∈ S, colour v ≠ colour w := by
    by_contra absent
    apply hm
    intro v hv w hw
    by_contra hne
    exact absent ⟨v, hv, w, hw, hne⟩
  have noMixed
      (hm : ((∃ v ∈ A, ∃ w ∈ A, colour v ≠ colour w) ∧ Mono B) ∨
        ((∃ v ∈ B, ∃ w ∈ B, colour v ≠ colour w) ∧ Mono A)) : False := by
    have hshape : ((∃ v w, wireVal n C (opnd C r 0) (unitInput v) = true ∧
        wireVal n C (opnd C r 0) (unitInput w) = true ∧ colour v ≠ colour w) ∧
        (∀ v w, wireVal n C (opnd C r 1) (unitInput v) = true →
          wireVal n C (opnd C r 1) (unitInput w) = true → colour v = colour w)) ∨
      ((∃ v w, wireVal n C (opnd C r 1) (unitInput v) = true ∧
        wireVal n C (opnd C r 1) (unitInput w) = true ∧ colour v ≠ colour w) ∧
        (∀ v w, wireVal n C (opnd C r 0) (unitInput v) = true →
          wireVal n C (opnd C r 0) (unitInput w) = true → colour v = colour w)) := by
      simp only [unitA, unitB]
      rcases hm with ⟨⟨v, hv, w, hw, hne⟩, hmono⟩ | ⟨⟨v, hv, w, hw, hne⟩, hmono⟩
      · exact Or.inl ⟨⟨v, w, hv, hw, hne⟩, fun x y hx hy => hmono x hx y hy⟩
      · exact Or.inr ⟨⟨v, w, hv, hw, hne⟩, fun x y hx hy => hmono x hx y hy⟩
    obtain ⟨D, hD, hsmaller, hfun⟩ := PEqualNP.Outside.L_meta_4743 n G C colour r hcolour h4
      H.ao H.comp H.lift H.andLow H.cone H.hg H.gand H.dirty H.others hunit hshape
    exact (Nat.not_lt_of_ge (h.2.2 D hD hfun)) hsmaller
  have bothMono : Mono A ∧ Mono B := by
    rcases someMono with hmono | hmono
    · refine ⟨hmono, ?_⟩
      by_contra hm
      exact noMixed (Or.inr ⟨mixed hm, hmono⟩)
    · refine ⟨?_, hmono⟩
      by_contra hm
      exact noMixed (Or.inl ⟨mixed hm, hmono⟩)
  obtain ⟨v, w, hv, hw, hvw⟩ : ∃ v w, v ∈ A ∧ w ∈ B ∧ G.Adj v w := by
    rcases oriented with ⟨huA, hzB⟩ | ⟨hzA, huB⟩
    · exact ⟨u, z, huA, hzB, huz⟩
    · exact ⟨z, u, hzA, huB, huz.symm⟩
  have colourA (t : Fin n) (ht : t ∈ A) : colour t = colour v := bothMono.1 t ht v hv
  have colourB (t : Fin n) (ht : t ∈ B) : colour t ≠ colour v := by
    rw [bothMono.2 t ht w hw]
    exact (hcolour v w hvw).symm
  have noSingleton (hs : (∃ t, A = {t}) ∨ (∃ t, B = {t})) : False := by
    have hshape :
        (∃ t, (∀ y, wireVal n C (opnd C r 1) (unitInput y) = true ↔ y = t) ∧
          ∀ y, wireVal n C (opnd C r 0) (unitInput y) = true → colour y ≠ colour t) ∨
        (∃ t, (∀ y, wireVal n C (opnd C r 0) (unitInput y) = true ↔ y = t) ∧
          ∀ y, wireVal n C (opnd C r 1) (unitInput y) = true → colour y ≠ colour t) := by
      simp only [unitA, unitB]
      rcases hs with ⟨t, ht⟩ | ⟨t, ht⟩
      · have hv' : v = t := by simpa [ht] using hv
        exact Or.inr ⟨t, fun y => by simp [ht], fun y hy => hv' ▸ colourB y hy⟩
      · have hw' : w = t := by simpa [ht] using hw
        refine Or.inl ⟨t, fun y => by simp [ht], fun y hy => ?_⟩
        rw [colourA y hy, ← hw']
        exact hcolour v w hvw
    obtain ⟨D, hD, hsmaller, hfun⟩ := PEqualNP.Outside.L_meta_4712 n G C colour r hcolour h4
      H.ao H.comp H.lift H.andLow H.cone H.hg H.gand H.dirty H.others hunit hshape
    exact (Nat.not_lt_of_ge (h.2.2 D hD hfun)) hsmaller
  have ha : 1 < A.card := by
    by_contra hsmall
    have hpos := Finset.card_pos.mpr hAn
    exact noSingleton (Or.inl (Finset.card_eq_one.mp (by omega)))
  have hb : 1 < B.card := by
    by_contra hsmall
    have hpos := Finset.card_pos.mpr hBn
    exact noSingleton (Or.inr (Finset.card_eq_one.mp (by omega)))
  exact ⟨a, b, A, B, colour v, hab, hA, hB, hd, ha, hb, colourA, colourB,
    z, centre, j, hj, hjand, hex⟩

/-- Fold the false junk value out of the exact AND/OR circuit. The junk and
    every immediate reader can be charged against the size, and each original
    wire is either identically false or represented by a wire of the result. -/
theorem foldSuspendedFalse {n : ℕ} (C : Circuit) (h : IsAO2 n C) {r : ℕ}
    {W : (Fin n → Bool) → ℕ → Bool} (hW : EvalExcept n C r W)
    (hzero : ∀ x, W x (n + r) = false)
    (dropped : Finset ℕ) (hd : dropped ⊆ Finset.range C.gates.length)
    (hdrop : ∀ j ∈ dropped, j = r ∨ n + r ∈ (gateAt C j).inputs) :
    ∃ gs : List Gate, IsAO2 n ⟨gs, 0⟩ ∧ gs.length + dropped.card ≤ C.gates.length ∧
      ∀ w < n + C.gates.length, Res gs (fun x => W x w) := by
  classical
  let K := (Finset.range C.gates.length).erase r
  let ρ := fun j d => if opnd C j d = n + r then none else srcOf n (opnd C j d)
  let P := progOf C ρ
  let value := fun j (x : Fin n → Bool) => W x (n + j)
  have source (x : Fin n → Bool) (j : ℕ) (d : Fin 2) :
      srcAt x (fun k => value k x) (ρ j d) = W x (opnd C j d) := by
    by_cases he : opnd C j d = n + r
    · simp [ρ, he, srcAt, hzero]
    · simp only [ρ, he, ite_false, srcOf]
      split_ifs with hw
      · exact (hW.1 x ⟨opnd C j d, hw⟩).symm
      · have heq : n + (opnd C j d - n) = opnd C j d := by omega
        change W x (n + (opnd C j d - n)) = W x (opnd C j d)
        rw [heq]
  have closed : Closed P id K := by
    intro j hj d k hk
    have hjlen := Finset.mem_range.mp (Finset.mem_erase.mp hj).2
    change ρ j d = some (Sum.inr k) at hk
    by_cases he : opnd C j d = n + r
    · simp [ρ, he] at hk
    · simp only [ρ, he, ite_false] at hk
      have heq := srcOf_inr _ _ hk
      have hlt := opnd_lt C h j hjlen d
      have hkj : k < j := by omega
      exact ⟨Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (hkj.trans hjlen)⟩, hkj⟩
  have sol : Sol P K value := by
    intro x j hj
    obtain ⟨hne, hj⟩ := Finset.mem_erase.mp hj
    have hjlen := Finset.mem_range.mp hj
    obtain ⟨p, q, hpq⟩ := twoOperands h hjlen
    change W x (n + j) = opv (isA (gateAt C j).op)
      (srcAt x (fun k => value k x) (ρ j 0)) (srcAt x (fun k => value k x) (ρ j 1))
    rw [source, source, hW.2 x j hjlen hne, hpq]
    rcases h.1 _ (gateAt_mem hjlen) with ho | ho <;> simp [ho, opnd, hpq, isA, opv, GateOp.eval]
  obtain ⟨gs, hgs, hlen, hres⟩ := PEqualNP.MetaComplexity.FoldProg.build P id value K closed sol
  have hkept : kept P value K ⊆ Finset.range C.gates.length :=
    (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
  have hdisj : Disjoint (kept P value K) dropped := by
    refine Finset.disjoint_left.mpr ?_
    intro j hj hjd
    obtain ⟨hjK, hleft, hright⟩ := Finset.mem_filter.mp hj
    rcases hdrop j hjd with rfl | hread
    · exact (Finset.mem_erase.mp hjK).1 rfl
    · have hjlen := Finset.mem_range.mp (Finset.mem_erase.mp hjK).2
      obtain ⟨d, hd⟩ := PEqualNP.MetaComplexity.LowerPart.mem_opnd C h j hjlen _ hread
      have hz : srcAt (fun _ => true) (fun k => value k fun _ => true) (ρ j d) = false := by
        simp [ρ, hd, srcAt]
      fin_cases d
      · exact Bool.false_ne_true (hz.symm.trans hleft)
      · exact Bool.false_ne_true (hz.symm.trans hright)
  have hcard := Finset.card_le_card (Finset.union_subset hkept hd)
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_range] at hcard
  refine ⟨gs, hgs, by omega, ?_⟩
  intro w hw
  by_cases hraw : w < n
  · let v : Fin n := ⟨w, hraw⟩
    exact Or.inr ⟨hW.1 _ v, w, by omega, fun x => (wireVal_input gs v x).trans (hW.1 x v).symm⟩
  · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    by_cases he : j = r
    · subst j
      exact Or.inl hzero
    · exact hres j (Finset.mem_erase.mpr ⟨he, Finset.mem_range.mpr (by omega)⟩)

/-- Erasing the junk and folding its readers strictly reduces the gate count
    when every edge survives the suspension. -/
theorem noOneJunkWithoutLostEdges {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    {r : ℕ} (hJ : junk G C = {r})
    {W : (Fin n → Bool) → ℕ → Bool} (hW : EvalExcept n C r W)
    (hzero : ∀ x, W x (n + r) = false)
    (hcover : ∀ u v, G.Adj u v → W (pairInput u v) C.output = true) : False := by
  classical
  have hr := (junkMember G C hJ).1
  have hout := outputLast G C h (Nat.zero_lt_of_lt hr)
  have houtBound : C.output < n + C.gates.length := by omega
  obtain ⟨gs, hao, hlen, hwires⟩ := foldSuspendedFalse C h.1 hW hzero {r}
    (by simpa using hr) (by intro j hj; exact Or.inl (Finset.mem_singleton.mp hj))
  have hlen' : gs.length + 1 ≤ C.gates.length := by simpa using hlen
  rcases hwires C.output houtBound with hfalse | ⟨_, w, _, hwire⟩
  · have hnone (u v : Fin n) (huv : G.Adj u v) : False :=
      Bool.false_ne_true ((hfalse _).symm.trans (hcover u v huv))
    have := emptyGraphNoGates G C h hnone
    omega
  · let D : Circuit := ⟨gs, w⟩
    have hD : IsAO2 n D := hao
    have hval (x : Fin n → Bool) : circuitFun n D x = W x C.output := hwire x
    have hcorrect : circuitFun n D = graphFun G ∅ := by
      funext x
      apply Bool.eq_iff_iff.mpr
      refine ⟨fun hx => suspendedFalseSound G C h hl hJ hW hzero x ((hval x).symm.trans hx), ?_⟩
      intro hx
      obtain ⟨u, v, hadj, hu, hv⟩ := (graph_true G x).mp hx
      apply circuit_monotone n D (ao_mono hD) (pairInput u v) x ?_ ((hval _).trans (hcover u v hadj))
      intro t ht
      have he : t = u ∨ t = v := by simpa [pairInput] using ht
      rcases he with rfl | rfl
      · exact hu
      · exact hv
    have hmin := h.2.2 D hD hcorrect
    change C.gates.length ≤ gs.length at hmin
    omega

/-- Two immediate readers pay for a strict one-star repair. The provider is
    preserved by the fold, so the repair uses at most one AND and one OR. -/
theorem noOneJunkOneStarWithTwoReaders {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    {r : ℕ} (hJ : junk G C = {r})
    {W : (Fin n → Bool) → ℕ → Bool} (hW : EvalExcept n C r W)
    (hzero : ∀ x, W x (n + r) = false)
    {j k : ℕ} (hj : j < C.gates.length) (hk : k < C.gates.length) (hjk : j ≠ k)
    (hjr : n + r ∈ (gateAt C j).inputs) (hkr : n + r ∈ (gateAt C k).inputs)
    {p : ℕ} (hp : p < n + C.gates.length) {S : Finset (Fin n)} (hS : RawForm C r p S false)
    (hne : S.Nonempty) (c : Fin n) (hadj : ∀ v ∈ S, G.Adj c v)
    (hcover : ∀ u v, G.Adj u v → W (pairInput u v) C.output = true ∨
      (pairInput u v c = true ∧ ∃ w ∈ S, pairInput u v w = true)) : False := by
  classical
  have hr := (junkMember G C hJ).1
  have hjr' : r ≠ j := by have := h.1.2.1 j hj _ hjr; omega
  have hkr' : r ≠ k := by have := h.1.2.1 k hk _ hkr; omega
  have hout := outputLast G C h (Nat.zero_lt_of_lt hr)
  have houtBound : C.output < n + C.gates.length := by omega
  obtain ⟨gs, hgs, hlen, hwires⟩ := foldSuspendedFalse C h.1 hW hzero {r, j, k}
    (by intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl <;> exact Finset.mem_range.mpr (by assumption))
    (by intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr hjr
        · exact Or.inr hkr)
  have hlen' : gs.length + 3 ≤ C.gates.length := by
    simpa [hjr', hkr', hjk] using hlen
  have hsupport (x : Fin n → Bool) : W x p = true ↔ ∃ v ∈ S, x v = true := by
    simpa using hS.2 W hW x
  obtain ⟨v, hv⟩ := hne
  have htop : W (fun _ => true) p = true := (hsupport _).mpr ⟨v, hv, rfl⟩
  rcases hwires p hp with hfalse | ⟨_, w, hw, hwire⟩
  · exact Bool.false_ne_true ((hfalse _).symm.trans htop)
  let star : Gate := ⟨GateOp.and, [c.val, w]⟩
  let base := gs ++ [star]
  let b := n + gs.length
  have hbase : IsAO2 n ⟨base, 0⟩ := isAO2_snoc gs GateOp.and (Or.inl rfl) _ _
    (by have := c.isLt; omega) hw hgs
  have hblen : base.length = gs.length + 1 := by simp [base]
  have hstar (x : Fin n → Bool) : wireVal n ⟨base, 0⟩ b x = true ↔
      x c = true ∧ ∃ v ∈ S, x v = true := by
    change wireVal n ⟨gs ++ [star], 0⟩ (n + gs.length) x = true ↔ _
    rw [wireVal_new]
    simp [star, GateOp.eval, wireVal_input gs c x, hwire x, hsupport x]
  have rebuilt : ∃ E : Circuit, IsAO2 n E ∧ E.gates.length ≤ gs.length + 2 ∧
      ∀ x, circuitFun n E x = true ↔
        W x C.output = true ∨ (x c = true ∧ ∃ v ∈ S, x v = true) := by
    rcases hwires C.output houtBound with hfalse | ⟨_, o, ho, hold⟩
    · refine ⟨⟨base, b⟩, hbase, by change base.length ≤ gs.length + 2; omega, fun x => ?_⟩
      change wireVal n ⟨base, 0⟩ b x = true ↔ _
      have hzeroOutput : W x C.output = false := hfalse x
      simp [hstar, hzeroOutput]
    · let join : Gate := ⟨GateOp.or, [o, b]⟩
      have ho' : o < n + base.length := by omega
      have hb' : b < n + base.length := by dsimp [b]; omega
      have hao := isAO2_snoc base GateOp.or (Or.inr rfl) o b ho' hb' hbase
      refine ⟨⟨base ++ [join], n + base.length⟩, hao, by simp [hblen], fun x => ?_⟩
      change wireVal n ⟨base ++ [join], 0⟩ (n + base.length) x = true ↔ _
      rw [wireVal_new]
      simp [join, GateOp.eval, wireVal_old gs star o ho x, base, hold x,
        show wireVal n ⟨gs ++ [star], 0⟩ b x = true ↔ _ from hstar x]
  obtain ⟨E, hE, hEsize, heval⟩ := rebuilt
  have hcorrect : circuitFun n E = graphFun G ∅ := by
    funext x
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hx
      rcases (heval x).mp hx with hy | ⟨hc, z, hz, hzx⟩
      · exact suspendedFalseSound G C h hl hJ hW hzero x hy
      · exact (graph_true G x).mpr ⟨c, z, hadj z hz, hc, hzx⟩
    · intro hx
      obtain ⟨u, z, huz, hu, hz⟩ := (graph_true G x).mp hx
      apply circuit_monotone n E (ao_mono hE) (pairInput u z) x ?_
        ((heval _).mpr (hcover u z huz))
      intro t ht
      have eq : t = u ∨ t = z := by simpa [pairInput] using ht
      rcases eq with rfl | rfl
      · exact hu
      · exact hz
  have hmin := h.2.2 E hE hcorrect
  change C.gates.length ≤ E.gates.length at hmin
  omega

#print axioms rawFormJunkReaches
#print axioms noSingletonOverlapWithUpstream
#print axioms oneJunkSupportsDisjoint
#print axioms oneJunkFalseOnUnit
#print axioms oneJunkHasEdgeReader
#print axioms oneJunkLargeOppositeSupports
#print axioms foldSuspendedFalse
#print axioms noOneJunkWithoutLostEdges
#print axioms noOneJunkOneStarWithTwoReaders

end ResearchVerification.OneJunkErase
