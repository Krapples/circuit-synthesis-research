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

/-- The gates that read the junk wire in an operand position. -/
def immediateJunkReaders {n : ℕ} (C : Circuit) (r : ℕ) : Finset ℕ :=
  (Finset.range C.gates.length).filter fun j => n + r ∈ (gateAt C j).inputs

/-- Two stars cover the losses, so a minimum circuit cannot yield any
    chargeable set larger than the cost of the two-star repair. -/
theorem oneJunkDroppedBudget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C) (h4 : NoFourCycle G)
    (colour : Fin n → Bool) (hcolour : ∀ u v, G.Adj u v → colour u ≠ colour v)
    {r : ℕ} (hJ : junk G C = {r}) {W : (Fin n → Bool) → ℕ → Bool}
    (hW : EvalExcept n C r W) (hzero : ∀ x, W x (n + r) = false)
    (dropped : Finset ℕ) (hd : dropped ⊆ Finset.range C.gates.length)
    (hdrop : ∀ j ∈ dropped, j = r ∨
      ∃ w ∈ (gateAt C j).inputs, W (fun _ => true) w = false) :
    dropped.card ≤ 3 + (W (fun _ => true) C.output).toNat := by
  classical
  by_contra! hmany
  obtain ⟨a, b, A, B, _, hab, hA, hB, hdisj, hcardA, hcardB, _⟩ :=
    oneJunkLargeOppositeSupports G C h hl h4 colour hcolour hJ
  obtain ⟨EA, EB, _, _, hEA, hEB, hadjA, hadjB, hclassification⟩ :=
    lostEdgesInExposedStars G C h hl h4 hJ hab hA hB hdisj hcardA hcardB
  let stars := EA.toList.map (fun c => (⟨c, B⟩ : RepairStar n)) ++
    EB.toList.map (fun c => (⟨c, A⟩ : RepairStar n))
  have hlength : stars.length ≤ 2 := by
    have he : stars.length = EA.card + EB.card := by simp [stars]
    omega
  have hkind (s : RepairStar n) (hs : s ∈ stars) :
      (s.centre ∈ EA ∧ s.support = B) ∨ (s.centre ∈ EB ∧ s.support = A) := by
    simp only [stars, List.mem_append, List.mem_map, Finset.mem_toList] at hs
    rcases hs with ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩
    · exact Or.inl ⟨hc, rfl⟩
    · exact Or.inr ⟨hc, rfl⟩
  have hcover (u v : Fin n) (huv : G.Adj u v) :
      W (pairInput u v) C.output = true ∨
      stars.any (fun s => RepairStar.fires s (pairInput u v)) = true := by
    let x := pairInput u v
    rcases (hclassification W hW hzero).2 u v huv with hv | ⟨c, hc, w, hw, hcx, hwx⟩ |
        ⟨c, hc, w, hw, hcx, hwx⟩
    · exact Or.inl hv
    · refine Or.inr (List.any_eq_true.mpr ⟨⟨c, B⟩, by simp [stars, hc], ?_⟩)
      change (x c && decide (∃ v ∈ B, x v = true)) = true
      have hhit : ∃ v ∈ B, x v = true := ⟨w, hw, hwx⟩
      simp [show x c = true from hcx, hhit]
    · refine Or.inr (List.any_eq_true.mpr ⟨⟨c, A⟩, by simp [stars, hc], ?_⟩)
      change (x c && decide (∃ v ∈ A, x v = true)) = true
      have hhit : ∃ v ∈ A, x v = true := ⟨w, hw, hwx⟩
      simp [show x c = true from hcx, hhit]
  by_cases hne : stars = []
  · apply noOneJunkWithoutLostEdges G C h hl hJ hW hzero
    intro u v huv
    simpa [hne] using hcover u v huv
  have hr := (junkMember G C hJ).1
  have ha : a < n + C.gates.length :=
    (h.1.2.1 r hr a (by simp [hab])).trans (Nat.add_lt_add_left hr n)
  have hb : b < n + C.gates.length :=
    (h.1.2.1 r hr b (by simp [hab])).trans (Nat.add_lt_add_left hr n)
  have hAn : A.Nonempty := Finset.card_pos.mp (by omega)
  have hBn : B.Nonempty := Finset.card_pos.mp (by omega)
  refine noOneJunkWithStarBudget G C h hl hJ hW hzero dropped hd hdrop stars hne ?_ ?_ hcover ?_
  · intro s hs
    rcases hkind s hs with ⟨_, he⟩ | ⟨_, he⟩
    · rw [he]
      exact ⟨hBn, b, hb, hB⟩
    · rw [he]
      exact ⟨hAn, a, ha, hA⟩
  · intro s hs v hv
    rcases hkind s hs with ⟨hm, he⟩ | ⟨hm, he⟩
    · exact hadjA _ hm v (he ▸ hv)
    · exact hadjB _ hm v (he ▸ hv)
  · cases htop : W (fun _ => true) C.output
    · right
      refine ⟨rfl, ?_⟩
      simp only [htop, Bool.toNat_false, Nat.add_zero] at hmany
      omega
    · left
      simp only [htop, Bool.toNat_true] at hmany
      omega

private theorem junkNotImmediateReader {n : ℕ} (C : Circuit) (h : IsAO2 n C) (r : ℕ) :
    r ∉ immediateJunkReaders (n := n) C r := by
  intro hm
  obtain ⟨hr, hread⟩ := Finset.mem_filter.mp hm
  exact (Nat.lt_irrefl _) (h.2.1 r (Finset.mem_range.mp hr) _ hread)

/-- Four immediate readers cannot occur, and three require a nonzero
    suspended output. -/
theorem oneJunkReaderBudget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C) (h4 : NoFourCycle G)
    (colour : Fin n → Bool) (hcolour : ∀ u v, G.Adj u v → colour u ≠ colour v)
    {r : ℕ} (hJ : junk G C = {r}) {W : (Fin n → Bool) → ℕ → Bool}
    (hW : EvalExcept n C r W) (hzero : ∀ x, W x (n + r) = false) :
    (immediateJunkReaders (n := n) C r).card ≤ 2 + (W (fun _ => true) C.output).toNat := by
  let R := immediateJunkReaders (n := n) C r
  have hr := (junkMember G C hJ).1
  have hsize := Finset.card_insert_of_notMem (junkNotImmediateReader C h.1 r)
  have hcount := oneJunkDroppedBudget G C h hl h4 colour hcolour hJ hW hzero (insert r R)
    (by intro j hj; rcases Finset.mem_insert.mp hj with rfl | hm
        · exact Finset.mem_range.mpr hr
        · exact (Finset.mem_filter.mp hm).1)
    (by intro j hj; rcases Finset.mem_insert.mp hj with rfl | hm
        · exact Or.inl rfl
        · exact Or.inr ⟨n + r, (Finset.mem_filter.mp hm).2, hzero _⟩)
  change (insert r (immediateJunkReaders (n := n) C r)).card ≤ _ at hcount
  rw [hsize] at hcount
  omega

theorem oneJunkAtMostThreeReaders {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C) (h4 : NoFourCycle G)
    (colour : Fin n → Bool) (hcolour : ∀ u v, G.Adj u v → colour u ≠ colour v)
    {r : ℕ} (hJ : junk G C = {r}) : (immediateJunkReaders (n := n) C r).card ≤ 3 := by
  obtain ⟨W, hW, hzero⟩ := existsEvalExceptWithJunk C h.1 r (fun _ => false)
  have hbound := oneJunkReaderBudget G C h hl h4 colour hcolour hJ hW hzero
  cases htop : W (fun _ => true) C.output <;> simp [htop] at hbound <;> omega

/-- A direct AND reader is forced to false by the suspension. When the
    suspended output survives, one of that reader's clean collector ORs
    also folds. This extra charge rules out three readers including an AND. -/
theorem oneJunkAtMostTwoWithAndReader {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C) (h4 : NoFourCycle G)
    (colour : Fin n → Bool) (hcolour : ∀ u v, G.Adj u v → colour u ≠ colour v)
    {r j : ℕ} (hJ : junk G C = {r}) (hj : j ∈ immediateJunkReaders (n := n) C r)
    (hand : (gateAt C j).op = GateOp.and) : (immediateJunkReaders (n := n) C r).card ≤ 2 := by
  obtain ⟨W, hW, hzero⟩ := existsEvalExceptWithJunk C h.1 r (fun _ => false)
  cases htop : W (fun _ => true) C.output
  · have hbound := oneJunkReaderBudget G C h hl h4 colour hcolour hJ hW hzero
    simpa [htop] using hbound
  · have H := fromLeastOneJunk G C h hl hJ
    obtain ⟨hjr, hread⟩ := Finset.mem_filter.mp hj
    have hjlen := Finset.mem_range.mp hjr
    have hrj : r < j := by have := h.1.2.1 j hjlen _ hread; omega
    have hclean := H.others j hjlen hand hrj.ne.symm
    obtain ⟨p, q, hpq⟩ := twoOperands h.1 hjlen
    let x : Fin n → Bool := fun _ => true
    have hjzero : W x (n + j) = false := by
      cases hv : W x (n + j)
      · rfl
      · obtain ⟨hp, hq⟩ := (evalExcept_and hW hjlen hrj.ne.symm hand hpq x).mp hv
        have he : n + r = p ∨ n + r = q := by simpa [hpq] using hread
        rcases he with he | he
        · rw [← he, hzero] at hp
          cases hp
        · rw [← he, hzero] at hq
          cases hq
    have hout : C.output ≠ n + j := by
      intro he
      have hv : W x C.output = true := htop
      rw [he, hjzero] at hv
      cases hv
    obtain ⟨k, hjk, hk, hkread⟩ := noUnreadGate G C h j (n + r) hjlen
      (h.1.2.1 j hjlen _ hread) hout
    obtain ⟨hkor, hkclean⟩ := cleanReader G C h hl hjlen hclean (allLive G C h k hk) hkread
    let R := immediateJunkReaders (n := n) C r
    have hknew : k ∉ insert r R := by
      intro hm
      rcases Finset.mem_insert.mp hm with he | hm
      · omega
      · exact H.dirty (cleanOrOperands G C h.1 hk hkor hkclean (Finset.mem_filter.mp hm).2)
    have hcount := oneJunkDroppedBudget G C h hl h4 colour hcolour hJ hW hzero (insert k (insert r R))
      (by intro i hi; rcases Finset.mem_insert.mp hi with rfl | hi
          · exact Finset.mem_range.mpr hk
          · rcases Finset.mem_insert.mp hi with rfl | hi
            · exact Finset.mem_range.mpr H.hg
            · exact (Finset.mem_filter.mp hi).1)
      (by intro i hi; rcases Finset.mem_insert.mp hi with rfl | hi
          · exact Or.inr ⟨n + j, hkread, hjzero⟩
          · rcases Finset.mem_insert.mp hi with rfl | hi
            · exact Or.inl rfl
            · exact Or.inr ⟨n + r, (Finset.mem_filter.mp hi).2, hzero _⟩)
    rw [Finset.card_insert_of_notMem hknew, Finset.card_insert_of_notMem
      (show r ∉ R from junkNotImmediateReader C h.1 r)] at hcount
    simp only [htop, Bool.toNat_true] at hcount
    change R.card ≤ 2
    omega

#print axioms rawFormJunkReaches
#print axioms noSingletonOverlapWithUpstream
#print axioms oneJunkSupportsDisjoint
#print axioms oneJunkFalseOnUnit
#print axioms oneJunkHasEdgeReader
#print axioms oneJunkLargeOppositeSupports
#print axioms oneJunkDroppedBudget
#print axioms oneJunkReaderBudget
#print axioms oneJunkAtMostThreeReaders
#print axioms oneJunkAtMostTwoWithAndReader

/-- The extra exclusive OR saving rules out three immediate readers
    in the remaining disjoint-support case. -/
theorem oneJunkAtMostTwoReaders {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C) (h4 : NoFourCycle G)
    (colour : Fin n → Bool) (hcolour : ∀ u v, G.Adj u v → colour u ≠ colour v)
    {r : ℕ} (hJ : junk G C = {r}) : (immediateJunkReaders (n := n) C r).card ≤ 2 := by
  classical
  by_contra! hcount
  let readers := immediateJunkReaders (n := n) C r
  change 2 < readers.card at hcount
  have hread (j) (hj : j ∈ readers) : j < C.gates.length ∧ n + r ∈ (gateAt C j).inputs := by
    obtain ⟨hj, hm⟩ := Finset.mem_filter.mp hj
    exact ⟨Finset.mem_range.mp hj, hm⟩
  obtain ⟨j, hj, k, hk, hjk⟩ := Finset.one_lt_card.mp (show 1 < readers.card by omega)
  obtain ⟨a, b, A, B, _, hab, hA, hB, hdisj, hcardA, hcardB, _⟩ :=
    oneJunkLargeOppositeSupports G C h hl h4 colour hcolour hJ
  obtain ⟨W, hW, hzero⟩ := existsEvalExceptWithJunk C h.1 r (fun _ => false)
  obtain ⟨EA, EB, hEA, hEB, hsmallA, hsmallB, hadjA, hadjB, hc⟩ :=
    lostEdgesInExposedStars G C h hl h4 hJ hab hA hB hdisj hcardA hcardB
  have classified := (hc W hW hzero).2
  have hr := (junkMember G C hJ).1
  have hal : a < n + C.gates.length :=
    (h.1.2.1 r hr a (by simp [hab])).trans (Nat.add_lt_add_left hr n)
  have hbl : b < n + C.gates.length :=
    (h.1.2.1 r hr b (by simp [hab])).trans (Nat.add_lt_add_left hr n)
  have oneStar {p : ℕ} (hp : p < n + C.gates.length) {S : Finset (Fin n)}
      (hS : RawForm C r p S false) (hn : S.Nonempty) (c : Fin n)
      (hstar : ∀ v ∈ S, G.Adj c v)
      (hcover : ∀ u v, G.Adj u v → W (pairInput u v) C.output = true ∨
        (pairInput u v c = true ∧ ∃ t ∈ S, pairInput u v t = true)) : False :=
    noOneJunkOneStarWithTwoReaders G C h hl hJ hW hzero (hread j hj).1 (hread k hk).1
      hjk (hread j hj).2 (hread k hk).2 hp hS hn c hstar hcover
  by_cases hAn : EA.Nonempty
  · obtain ⟨s, hs⟩ := hAn
    have hAonly (t) (ht : t ∈ EA) := Finset.card_le_one.mp hsmallA t ht s hs
    by_cases hBn : EB.Nonempty
    · obtain ⟨d, hd⟩ := hBn
      have hBonly (t) (ht : t ∈ EB) := Finset.card_le_one.mp hsmallB t ht d hd
      have cover (u v) (huv : G.Adj u v) : W (pairInput u v) C.output = true ∨
          (pairInput u v s = true ∧ ∃ t ∈ B, pairInput u v t = true) ∨
          (pairInput u v d = true ∧ ∃ t ∈ A, pairInput u v t = true) := by
        rcases classified u v huv with ho | ⟨c, hc, t, ht, hcx, htx⟩ | ⟨c, hc, t, ht, hcx, htx⟩
        · exact Or.inl ho
        · exact Or.inr (Or.inl ⟨hAonly c hc ▸ hcx, t, ht, htx⟩)
        · exact Or.inr (Or.inr ⟨hBonly c hc ▸ hcx, t, ht, htx⟩)
      by_cases hall : ∀ t ∈ A, W (pairInput t d) C.output = true
      · apply oneStar hbl hB ⟨d, hEB hd⟩ s (hadjA s hs)
        intro u v huv
        rcases cover u v huv with ho | hstar | ⟨hdx, t, ht, htx⟩
        · exact Or.inl ho
        · exact Or.inr hstar
        have hne := G.ne_of_adj (hadjB d hd t ht).symm
        have htuv : t = u ∨ t = v := by simpa [pairInput] using htx
        have hduv : d = u ∨ d = v := by simpa [pairInput] using hdx
        rcases htuv with htu | htv <;> rcases hduv with hdu | hdv
        · exact (hne (htu.trans hdu.symm)).elim
        · exact Or.inl (by simpa [htu, hdv] using hall t ht)
        · have he : pairInput v u = pairInput u v := by
            funext w
            simp [pairInput, or_comm]
          exact Or.inl (by simpa [htv, hdu, he] using hall t ht)
        · exact (hne (htv.trans hdv.symm)).elim
      · push Not at hall
        obtain ⟨t, ht, hfalse⟩ := hall
        exact noOneJunkWithTrimmedTwoStars G C h hl h4 hJ hab hA hB hdisj hcardA
          (hEA hs) (hEB hd) (hadjA s hs) (fun u hu => (hadjB d hd u hu).symm) hW hzero
          ⟨t, ht, by cases hv : W (pairInput t d) C.output <;> simp_all⟩ cover
          readers (by omega) hread
    · apply oneStar hbl hB (Finset.card_pos.mp (by omega)) s (hadjA s hs)
      intro u v huv
      rcases classified u v huv with ho | ⟨c, hc, t, ht, hcx, htx⟩ | ⟨c, hc, _⟩
      · exact Or.inl ho
      · exact Or.inr ⟨hAonly c hc ▸ hcx, t, ht, htx⟩
      · exact (hBn ⟨c, hc⟩).elim
  · by_cases hBn : EB.Nonempty
    · obtain ⟨d, hd⟩ := hBn
      have hBonly (t) (ht : t ∈ EB) := Finset.card_le_one.mp hsmallB t ht d hd
      apply oneStar hal hA (Finset.card_pos.mp (by omega)) d (hadjB d hd)
      intro u v huv
      rcases classified u v huv with ho | ⟨c, hc, _⟩ | ⟨c, hc, t, ht, hcx, htx⟩
      · exact Or.inl ho
      · exact (hAn ⟨c, hc⟩).elim
      · exact Or.inr ⟨hBonly c hc ▸ hcx, t, ht, htx⟩
    · apply noOneJunkWithoutLostEdges G C h hl hJ hW hzero
      intro u v huv
      rcases classified u v huv with ho | ⟨c, hc, _⟩ | ⟨c, hc, _⟩
      · exact ho
      · exact (hAn ⟨c, hc⟩).elim
      · exact (hBn ⟨c, hc⟩).elim

#print axioms oneJunkAtMostTwoReaders

/-- With a direct AND reader, two direct readers are impossible.
    The collector fold is a post-junk charge distinct from the pre-junk trim. -/
theorem oneJunkAtMostOneWithAndReader {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C) (h4 : NoFourCycle G)
    (colour : Fin n → Bool) (hcolour : ∀ u v, G.Adj u v → colour u ≠ colour v)
    {r i : ℕ} (hJ : junk G C = {r})
    (hi : i ∈ immediateJunkReaders (n := n) C r)
    (hand : (gateAt C i).op = GateOp.and) :
    (immediateJunkReaders (n := n) C r).card ≤ 1 := by
  classical
  by_contra! hcount
  let readers := immediateJunkReaders (n := n) C r
  change 1 < readers.card at hcount
  have hread (j) (hj : j ∈ readers) : j < C.gates.length ∧ n + r ∈ (gateAt C j).inputs := by
    obtain ⟨hj, hm⟩ := Finset.mem_filter.mp hj
    exact ⟨Finset.mem_range.mp hj, hm⟩
  obtain ⟨j, hj, k, hk, hjk⟩ := Finset.one_lt_card.mp (show 1 < readers.card by omega)
  obtain ⟨a, b, A, B, _, hab, hA, hB, hdisj, hcardA, hcardB, _⟩ :=
    oneJunkLargeOppositeSupports G C h hl h4 colour hcolour hJ
  obtain ⟨W, hW, hzero⟩ := existsEvalExceptWithJunk C h.1 r (fun _ => false)
  obtain ⟨EA, EB, hEA, hEB, hsmallA, hsmallB, hadjA, hadjB, hc⟩ :=
    lostEdgesInExposedStars G C h hl h4 hJ hab hA hB hdisj hcardA hcardB
  have classified := (hc W hW hzero).2
  have hcharges : ∃ charges : Finset ℕ, 2 ≤ charges.card ∧
      (3 ≤ charges.card ∨ W (fun _ => true) C.output = false) ∧
      ∀ q ∈ charges, r < q ∧ q < C.gates.length ∧
        ∃ w ∈ (gateAt C q).inputs, W (fun _ => true) w = false := by
    have hbase (q) (hq : q ∈ readers) : r < q ∧ q < C.gates.length ∧
        ∃ w ∈ (gateAt C q).inputs, W (fun _ => true) w = false := by
      obtain ⟨hql, hqm⟩ := hread q hq
      exact ⟨Nat.lt_of_add_lt_add_left (h.1.2.1 q hql _ hqm), hql, n+r, hqm, hzero _⟩
    cases htop : W (fun _ => true) C.output
    · exact ⟨readers, by omega, Or.inr rfl, hbase⟩
    · have H := fromLeastOneJunk G C h hl hJ
      obtain ⟨hri, hil, w, hw, hwzero⟩ := hbase i hi
      have hclean := H.others i hil hand hri.ne.symm
      obtain ⟨p, q, hpq⟩ := twoOperands h.1 hil
      let x : Fin n → Bool := fun _ => true
      have hizero : W x (n+i) = false := by
        cases hv : W x (n+i)
        · rfl
        · obtain ⟨hp,hq⟩ := (evalExcept_and hW hil hri.ne.symm hand hpq x).mp hv
          have he : w = p ∨ w = q := by simpa [hpq] using hw
          rcases he with rfl | rfl
          · rw [hwzero] at hp
            cases hp
          · rw [hwzero] at hq
            cases hq
      have hout : C.output ≠ n+i := by
        intro he
        have hv : W x C.output = true := htop
        rw [he,hizero] at hv
        cases hv
      obtain ⟨t,hit,ht,htread⟩ := noUnreadGate G C h i (n+r) hil
        (h.1.2.1 i hil _ (hread i hi).2) hout
      obtain ⟨hor,hct⟩ := cleanReader G C h hl hil hclean (allLive G C h t ht) htread
      have htnot : t ∉ readers := by
        intro hm
        exact H.dirty (cleanOrOperands G C h.1 ht hor hct (hread t hm).2)
      refine ⟨insert t readers, ?_, Or.inl ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem htnot]
        omega
      · rw [Finset.card_insert_of_notMem htnot]
        omega
      · intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact ⟨by omega, ht, n+i, htread, hizero⟩
        · exact hbase z hz
  obtain ⟨charges,hcc,hbudget,hcharge⟩ := hcharges

  have hr := (junkMember G C hJ).1
  have hal : a < n + C.gates.length :=
    (h.1.2.1 r hr a (by simp [hab])).trans (Nat.add_lt_add_left hr n)
  have hbl : b < n + C.gates.length :=
    (h.1.2.1 r hr b (by simp [hab])).trans (Nat.add_lt_add_left hr n)
  have oneStar {p : ℕ} (hp : p < n + C.gates.length) {S : Finset (Fin n)}
      (hS : RawForm C r p S false) (hn : S.Nonempty) (c : Fin n)
      (hstar : ∀ v ∈ S, G.Adj c v)
      (hcover : ∀ u v, G.Adj u v → W (pairInput u v) C.output = true ∨
        (pairInput u v c = true ∧ ∃ t ∈ S, pairInput u v t = true)) : False :=
    noOneJunkOneStarWithTwoReaders G C h hl hJ hW hzero (hread j hj).1 (hread k hk).1
      hjk (hread j hj).2 (hread k hk).2 hp hS hn c hstar hcover
  by_cases hAn : EA.Nonempty
  · obtain ⟨s, hs⟩ := hAn
    have hAonly (t) (ht : t ∈ EA) := Finset.card_le_one.mp hsmallA t ht s hs
    by_cases hBn : EB.Nonempty
    · obtain ⟨d, hd⟩ := hBn
      have hBonly (t) (ht : t ∈ EB) := Finset.card_le_one.mp hsmallB t ht d hd
      have cover (u v) (huv : G.Adj u v) : W (pairInput u v) C.output = true ∨
          (pairInput u v s = true ∧ ∃ t ∈ B, pairInput u v t = true) ∨
          (pairInput u v d = true ∧ ∃ t ∈ A, pairInput u v t = true) := by
        rcases classified u v huv with ho | ⟨c, hc, t, ht, hcx, htx⟩ | ⟨c, hc, t, ht, hcx, htx⟩
        · exact Or.inl ho
        · exact Or.inr (Or.inl ⟨hAonly c hc ▸ hcx, t, ht, htx⟩)
        · exact Or.inr (Or.inr ⟨hBonly c hc ▸ hcx, t, ht, htx⟩)
      by_cases hall : ∀ t ∈ A, W (pairInput t d) C.output = true
      · apply oneStar hbl hB ⟨d, hEB hd⟩ s (hadjA s hs)
        intro u v huv
        rcases cover u v huv with ho | hstar | ⟨hdx, t, ht, htx⟩
        · exact Or.inl ho
        · exact Or.inr hstar
        have hne := G.ne_of_adj (hadjB d hd t ht).symm
        have htuv : t = u ∨ t = v := by simpa [pairInput] using htx
        have hduv : d = u ∨ d = v := by simpa [pairInput] using hdx
        rcases htuv with htu | htv <;> rcases hduv with hdu | hdv
        · exact (hne (htu.trans hdu.symm)).elim
        · exact Or.inl (by simpa [htu, hdv] using hall t ht)
        · have he : pairInput v u = pairInput u v := by
            funext w
            simp [pairInput, or_comm]
          exact Or.inl (by simpa [htv, hdu, he] using hall t ht)
        · exact (hne (htv.trans hdv.symm)).elim
      · push Not at hall
        obtain ⟨t, ht, hfalse⟩ := hall
        exact noOneJunkWithTrimmedTwoStarsBudget G C h hl h4 hJ hab hA hB hdisj hcardA
          (hEA hs) (hEB hd) (hadjA s hs) (fun u hu => (hadjB d hd u hu).symm) hW hzero
          ⟨t, ht, by cases hv : W (pairInput t d) C.output <;> simp_all⟩ cover
          charges hcc hbudget hcharge
    · apply oneStar hbl hB (Finset.card_pos.mp (by omega)) s (hadjA s hs)
      intro u v huv
      rcases classified u v huv with ho | ⟨c, hc, t, ht, hcx, htx⟩ | ⟨c, hc, _⟩
      · exact Or.inl ho
      · exact Or.inr ⟨hAonly c hc ▸ hcx, t, ht, htx⟩
      · exact (hBn ⟨c, hc⟩).elim
  · by_cases hBn : EB.Nonempty
    · obtain ⟨d, hd⟩ := hBn
      have hBonly (t) (ht : t ∈ EB) := Finset.card_le_one.mp hsmallB t ht d hd
      apply oneStar hal hA (Finset.card_pos.mp (by omega)) d (hadjB d hd)
      intro u v huv
      rcases classified u v huv with ho | ⟨c, hc, _⟩ | ⟨c, hc, t, ht, hcx, htx⟩
      · exact Or.inl ho
      · exact (hAn ⟨c, hc⟩).elim
      · exact Or.inr ⟨hBonly c hc ▸ hcx, t, ht, htx⟩
    · apply noOneJunkWithoutLostEdges G C h hl hJ hW hzero
      intro u v huv
      rcases classified u v huv with ho | ⟨c, hc, _⟩ | ⟨c, hc, _⟩
      · exact ho
      · exact (hAn ⟨c, hc⟩).elim
      · exact (hBn ⟨c, hc⟩).elim

#print axioms oneJunkAtMostOneWithAndReader


/-- An AND reader cannot be paid for by zero or one star. If such a
    reader survives as a candidate, both exposed stars have a private
    noncentral edge lost under false suspension. -/
private theorem oneJunkNeedsBothStars {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    (h4 : NoFourCycle G) (colour : Fin n → Bool)
    (hcolour : ∀ u v, G.Adj u v → colour u ≠ colour v)
    {r : ℕ} (hJ : junk G C = {r})
    (hpay : ∀ {W : (Fin n → Bool) → ℕ → Bool}, EvalExcept n C r W →
      (∀ x, W x (n+r) = false) →
      ∀ {p : ℕ}, p < n+C.gates.length → ∀ {S : Finset (Fin n)}, RawForm C r p S false →
      S.Nonempty → ∀ c : Fin n, (∀ v ∈ S, G.Adj c v) →
      (∀ u v, G.Adj u v → W (pairInput u v) C.output = true ∨
        (pairInput u v c = true ∧ ∃ t ∈ S, pairInput u v t = true)) → False) :
    ∃ a b : ℕ, ∃ A B : Finset (Fin n), ∃ s d u v : Fin n,
      ∃ W : (Fin n → Bool) → ℕ → Bool,
      (gateAt C r).inputs = [a,b] ∧ RawForm C r a A false ∧ RawForm C r b B false ∧
      Disjoint A B ∧ 1 < A.card ∧ 1 < B.card ∧
      s ∈ A ∧ d ∈ B ∧ u ∈ A ∧ v ∈ B ∧ u ≠ s ∧ v ≠ d ∧
      (∀ z ∈ B, G.Adj s z) ∧ (∀ z ∈ A, G.Adj d z) ∧
      EvalExcept n C r W ∧ (∀ x, W x (n+r) = false) ∧
      W (pairInput u d) C.output = false ∧ W (pairInput s v) C.output = false ∧
      (∀ p q, G.Adj p q → W (pairInput p q) C.output = true ∨
        (pairInput p q s = true ∧ ∃ t ∈ B, pairInput p q t = true) ∨
        (pairInput p q d = true ∧ ∃ t ∈ A, pairInput p q t = true)) := by
  classical
  obtain ⟨a, b, A, B, _, hab, hA, hB, hdisj, hcardA, hcardB, _⟩ :=
    oneJunkLargeOppositeSupports G C h hl h4 colour hcolour hJ
  obtain ⟨W, hW, hzero⟩ := existsEvalExceptWithJunk C h.1 r (fun _ => false)
  obtain ⟨EA, EB, hEA, hEB, hsmallA, hsmallB, hadjA, hadjB, hc⟩ :=
    lostEdgesInExposedStars G C h hl h4 hJ hab hA hB hdisj hcardA hcardB
  have classified := (hc W hW hzero).2
  have hr := (junkMember G C hJ).1
  have hal : a < n + C.gates.length :=
    (h.1.2.1 r hr a (by simp [hab])).trans (Nat.add_lt_add_left hr n)
  have hbl : b < n + C.gates.length :=
    (h.1.2.1 r hr b (by simp [hab])).trans (Nat.add_lt_add_left hr n)
  have oneStar {p : ℕ} (hp : p < n + C.gates.length) {S : Finset (Fin n)}
      (hS : RawForm C r p S false) (hn : S.Nonempty) (c : Fin n)
      (hstar : ∀ v ∈ S, G.Adj c v)
      (hcover : ∀ u v, G.Adj u v → W (pairInput u v) C.output = true ∨
        (pairInput u v c = true ∧ ∃ t ∈ S, pairInput u v t = true)) : False :=
    hpay hW hzero hp hS hn c hstar hcover
  by_cases hAn : EA.Nonempty
  · obtain ⟨s, hs⟩ := hAn
    have hAonly (t) (ht : t ∈ EA) := Finset.card_le_one.mp hsmallA t ht s hs
    by_cases hBn : EB.Nonempty
    · obtain ⟨d, hd⟩ := hBn
      have hBonly (t) (ht : t ∈ EB) := Finset.card_le_one.mp hsmallB t ht d hd
      have cover (u v) (huv : G.Adj u v) : W (pairInput u v) C.output = true ∨
          (pairInput u v s = true ∧ ∃ t ∈ B, pairInput u v t = true) ∨
          (pairInput u v d = true ∧ ∃ t ∈ A, pairInput u v t = true) := by
        rcases classified u v huv with ho | ⟨c, hc, t, ht, hcx, htx⟩ | ⟨c, hc, t, ht, hcx, htx⟩
        · exact Or.inl ho
        · exact Or.inr (Or.inl ⟨hAonly c hc ▸ hcx, t, ht, htx⟩)
        · exact Or.inr (Or.inr ⟨hBonly c hc ▸ hcx, t, ht, htx⟩)

      have pairEq (u v p q : Fin n) (hp : pairInput u v p = true)
          (hq : pairInput u v q = true) (hne : p ≠ q) :
          pairInput u v = pairInput p q := by
        have hp' : p = u ∨ p = v := by simpa [pairInput] using hp
        have hq' : q = u ∨ q = v := by simpa [pairInput] using hq
        rcases hp' with hp' | hp' <;> rcases hq' with hq' | hq'
        · exact (hne (hp'.trans hq'.symm)).elim
        · simp [hp',hq']
        · funext w
          simp [pairInput,hp',hq',or_comm]
        · exact (hne (hp'.trans hq'.symm)).elim
      have hmissingA : ∃ v ∈ B, W (pairInput s v) C.output = false ∧ v ≠ d := by
        by_contra hn
        apply oneStar hal hA ⟨s,hEA hs⟩ d (hadjB d hd)
        intro u v huv
        rcases cover u v huv with ho | ⟨hsx,z,hz,hzx⟩ | hstar
        · exact Or.inl ho
        · by_cases hzd : z = d
          · exact Or.inr ⟨hzd ▸ hzx,s,hEA hs,hsx⟩
          · left
            rw [pairEq u v s z hsx hzx (G.ne_of_adj (hadjA s hs z hz))]
            cases he : W (pairInput s z) C.output
            · exact (hn ⟨z,hz,he,hzd⟩).elim
            · rfl
        · exact Or.inr hstar
      have hmissingB : ∃ u ∈ A, W (pairInput u d) C.output = false ∧ u ≠ s := by
        by_contra hn
        apply oneStar hbl hB ⟨d,hEB hd⟩ s (hadjA s hs)
        intro u v huv
        rcases cover u v huv with ho | hstar | ⟨hdx,z,hz,hzx⟩
        · exact Or.inl ho
        · exact Or.inr hstar
        · by_cases hzs : z = s
          · exact Or.inr ⟨hzs ▸ hzx,d,hEB hd,hdx⟩
          · left
            rw [pairEq u v z d hzx hdx (G.ne_of_adj (hadjB d hd z hz).symm)]
            cases he : W (pairInput z d) C.output
            · exact (hn ⟨z,hz,he,hzs⟩).elim
            · rfl
      obtain ⟨v,hv,hvf,hvd⟩ := hmissingA
      obtain ⟨u,hu,huf,hus⟩ := hmissingB
      exact ⟨a,b,A,B,s,d,u,v,W,hab,hA,hB,hdisj,hcardA,hcardB,hEA hs,hEB hd,
        hu,hv,hus,hvd,hadjA s hs,hadjB d hd,hW,hzero,huf,hvf,cover⟩
    · exfalso
      apply oneStar hbl hB (Finset.card_pos.mp (by omega)) s (hadjA s hs)
      intro u v huv
      rcases classified u v huv with ho | ⟨c, hc, t, ht, hcx, htx⟩ | ⟨c, hc, _⟩
      · exact Or.inl ho
      · exact Or.inr ⟨hAonly c hc ▸ hcx, t, ht, htx⟩
      · exact (hBn ⟨c, hc⟩).elim
  · by_cases hBn : EB.Nonempty
    · obtain ⟨d, hd⟩ := hBn
      have hBonly (t) (ht : t ∈ EB) := Finset.card_le_one.mp hsmallB t ht d hd
      exfalso
      apply oneStar hal hA (Finset.card_pos.mp (by omega)) d (hadjB d hd)
      intro u v huv
      rcases classified u v huv with ho | ⟨c, hc, _⟩ | ⟨c, hc, t, ht, hcx, htx⟩
      · exact Or.inl ho
      · exact (hAn ⟨c, hc⟩).elim
      · exact Or.inr ⟨hBonly c hc ▸ hcx, t, ht, htx⟩
    · exfalso
      apply noOneJunkWithoutLostEdges G C h hl hJ hW hzero
      intro u v huv
      rcases classified u v huv with ho | ⟨c, hc, _⟩ | ⟨c, hc, _⟩
      · exact ho
      · exact (hAn ⟨c, hc⟩).elim
      · exact (hBn ⟨c, hc⟩).elim


theorem oneJunkAndReaderNeedsBothStars {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    (h4 : NoFourCycle G) (colour : Fin n → Bool)
    (hcolour : ∀ u v, G.Adj u v → colour u ≠ colour v)
    {r i : ℕ} (hJ : junk G C = {r})
    (hi : i ∈ immediateJunkReaders (n := n) C r)
    (hand : (gateAt C i).op = GateOp.and) :
    ∃ a b : ℕ, ∃ A B : Finset (Fin n), ∃ s d u v : Fin n,
      ∃ W : (Fin n → Bool) → ℕ → Bool,
      (gateAt C r).inputs = [a,b] ∧ RawForm C r a A false ∧ RawForm C r b B false ∧
      Disjoint A B ∧ 1 < A.card ∧ 1 < B.card ∧
      s ∈ A ∧ d ∈ B ∧ u ∈ A ∧ v ∈ B ∧ u ≠ s ∧ v ≠ d ∧
      (∀ z ∈ B, G.Adj s z) ∧ (∀ z ∈ A, G.Adj d z) ∧
      EvalExcept n C r W ∧ (∀ x, W x (n+r) = false) ∧
      W (pairInput u d) C.output = false ∧ W (pairInput s v) C.output = false ∧
      (∀ p q, G.Adj p q → W (pairInput p q) C.output = true ∨
        (pairInput p q s = true ∧ ∃ t ∈ B, pairInput p q t = true) ∨
        (pairInput p q d = true ∧ ∃ t ∈ A, pairInput p q t = true)) := by
  obtain ⟨hir,him⟩ := Finset.mem_filter.mp hi
  have hil := Finset.mem_range.mp hir
  apply oneJunkNeedsBothStars G C h hl h4 colour hcolour hJ
  intro W hW hzero p hp S hS hn c hstar hcover
  exact noOneJunkOneStarWithAndReader G C h hl hJ hW hzero hil him hand hp hS hn c hstar hcover

#print axioms oneJunkAndReaderNeedsBothStars


/-- A direct AND reader is impossible: it is the sole reader by the
    earlier bound, and both necessary stars force its opposite input
    to be an exclusive mixed-colour provider. -/
theorem noOneJunkAndReader {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C) (h4 : NoFourCycle G)
    (colour : Fin n → Bool) (hcolour : ∀ u v, G.Adj u v → colour u ≠ colour v)
    {r i : ℕ} (hJ : junk G C = {r})
    (hi : i ∈ immediateJunkReaders (n := n) C r)
    (hand : (gateAt C i).op = GateOp.and) : False := by
  classical
  have H := fromLeastOneJunk G C h hl hJ
  obtain ⟨hir,him⟩ := Finset.mem_filter.mp hi
  have hil := Finset.mem_range.mp hir
  have hri : r < i := Nat.lt_of_add_lt_add_left (h.1.2.1 i hil _ him)
  have hic := H.others i hil hand hri.ne.symm
  have hcard := oneJunkAtMostOneWithAndReader G C h hl h4 colour hcolour hJ hi hand
  have onlyReader (j) (hj : j < C.gates.length) (hm : n+r ∈ (gateAt C j).inputs) : j = i :=
    Finset.card_le_one.mp hcard j (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,hm⟩) i hi
  have hno (j) (hj : j < C.gates.length) (hor : (gateAt C j).op = GateOp.or) :
      n+r ∉ (gateAt C j).inputs := by
    intro hm
    have he := onlyReader j hj hm
    rw [he,hand] at hor
    cases hor
  obtain ⟨a,b,A,B,s,d,u,v,W,hab,hA,hB,hdisj,hcardA,hcardB,hs,hd,hu,hv,hus,hvd,
    hstarA,hstarB,hW,hzero,hmissB,hmissA,hcover⟩ :=
    oneJunkAndReaderNeedsBothStars G C h hl h4 colour hcolour hJ hi hand
  obtain ⟨p,q,hpq⟩ := twoOperands h.1 hil
  obtain ⟨w,hiw⟩ : ∃ w, (gateAt C i).inputs = [n+r,w] ∨
      (gateAt C i).inputs = [w,n+r] := by
    rcases (show n+r = p ∨ n+r = q by simpa [hpq] using him) with he | he
    · exact ⟨q,Or.inl (by simpa [he] using hpq)⟩
    · exact ⟨p,Or.inr (by simpa [he] using hpq)⟩
  have hwm : w ∈ (gateAt C i).inputs := by
    rcases hiw with he | he <;> simp [he]
  have hwn : w ≠ n+r := by
    intro he
    apply distinctOperands G C h (a := n+r) hil
    rcases hiw with hh | hh <;> simpa [he] using hh
  have hwlt := h.1.2.1 i hil w hwm
  have hwd := noCleanAndOperand G C h i w hil hwm hand
  obtain ⟨T,hT⟩ := dirtyRawFormNoOrReader G C h hl hJ hno w (by omega) hwn hwd
  let V := fun (x : Fin n → Bool) k => val C (List.ofFn x) k
  have hV : EvalExcept n C r V := originalEvalExcept h.1 r
  have htop (U : (Fin n → Bool) → ℕ → Bool) (hU : EvalExcept n C r U) (x : Fin n → Bool) :
      U x (n+i) = true ↔ U x (n+r) = true ∧ U x w = true := by
    rcases hiw with he | he
    · exact evalExcept_and hU hil hri.ne.symm hand he x
    · rw [evalExcept_and hU hil hri.ne.symm hand he x]
      exact and_comm
  have lostTop (x : Fin n → Bool) (hx : graphFun G ∅ x = true)
      (hf : W x C.output = false) : V x (n+i) = true := by
    have ho : V x C.output = true := (congrFun h.2.1 x).trans hx
    obtain ⟨j,hj,hja,hjc,hjv⟩ := (collectorSemantics G C h hl hJ hV x).mp ho
    by_cases hm : n+r ∈ (gateAt C j).inputs
    · simpa [onlyReader j hj hm] using hjv
    · have he := cleanTopUnaffectedNoOrReader G C h hl hJ hno hj hja hjc hm hV hW x
      have ht := (collectorSemantics G C h hl hJ hW x).mpr ⟨j,hj,hja,hjc,he.symm.trans hjv⟩
      rw [hf] at ht
      cases ht
  have hpair (x y : Fin n) (hx : x ∈ A) (hy : y ∈ B) :
      V (pairInput x y) (n+r) = true :=
    (junkAtPair h.1 H.hg H.gand hab hA hB x y).mpr ⟨Or.inl hx,Or.inr hy⟩
  have forcedAdj (x y : Fin n) (hx : x ∈ A) (hy : y ∈ B)
      (ht : x ∈ T ∨ y ∈ T) : G.Adj x y := by
    have hw : V (pairInput x y) w = true := by
      apply (hT.2 V hV _).mpr
      rcases ht with ht | ht
      · exact Or.inl ⟨x,ht,by simp [pairInput]⟩
      · exact Or.inl ⟨y,ht,by simp [pairInput]⟩
    exact PEqualNP.Outside.L_meta_4745.pair_adj G x y
      (hic _ ((htop V hV _).mpr ⟨hpair x y hx hy,hw⟩))
  have hitsT (x y : Fin n) (ha : G.Adj x y) (hf : W (pairInput x y) C.output = false) :
      x ∈ T ∨ y ∈ T := by
    have ht := (htop V hV _).mp (lostTop _ (pair_true G x y ha) hf)
    obtain ⟨z,hz,hzx⟩ := ((hT.2 V hV _).mp ht.2).resolve_right (by simp)
    rcases (show z = x ∨ z = y by simpa [pairInput] using hzx) with rfl | rfl
    · exact Or.inl hz
    · exact Or.inr hz
  have uniqueA (x : Fin n) (hx : x ∈ A) (ht : x ∈ T) : x = s := by
    obtain ⟨e,he,f,hf,hef⟩ := Finset.one_lt_card.mp hcardB
    let S := Finset.univ.filter fun z => G.Adj e z ∧ G.Adj f z
    have hS : S.card ≤ 1 := h4 e f hef
    have hxS : x ∈ S := by
      simp [S,(forcedAdj x e hx he (Or.inl ht)).symm,
        (forcedAdj x f hx hf (Or.inl ht)).symm]
    have hsS : s ∈ S := by simp [S,(hstarA e he).symm,(hstarA f hf).symm]
    exact Finset.card_le_one.mp hS x hxS s hsS
  have uniqueB (y : Fin n) (hy : y ∈ B) (ht : y ∈ T) : y = d := by
    obtain ⟨e,he,f,hf,hef⟩ := Finset.one_lt_card.mp hcardA
    let S := Finset.univ.filter fun z => G.Adj e z ∧ G.Adj f z
    have hS : S.card ≤ 1 := h4 e f hef
    have hyS : y ∈ S := by
      simp [S,forcedAdj e y he hy (Or.inr ht),forcedAdj f y hf hy (Or.inr ht)]
    have hdS : d ∈ S := by simp [S,(hstarB e he).symm,(hstarB f hf).symm]
    exact Finset.card_le_one.mp hS y hyS d hdS
  have hdT : d ∈ T := (hitsT u d (hstarB u hu).symm hmissB).resolve_left
    (fun ht => hus (uniqueA u hu ht))
  have hsT : s ∈ T := (hitsT s v (hstarA v hv) hmissA).resolve_right
    (fun ht => hvd (uniqueB v hv ht))
  have hsd : s ≠ d := G.ne_of_adj (hstarA d hd)
  have hng : n ≤ w := by
    by_contra! hn
    let z : Fin n := ⟨w,hn⟩
    have ident (t : Fin n) (ht : t ∈ T) : z = t := by
      have hval := (hT.2 W hW (pairInput t t)).mpr (Or.inl ⟨t,ht,by simp [pairInput]⟩)
      simpa [pairInput] using (hW.1 (pairInput t t) z).symm.trans hval
    exact hsd ((ident s hsT).symm.trans (ident d hdT))
  obtain ⟨j,rfl⟩ : ∃ j, w = n+j := ⟨w-n,by omega⟩
  have hj : j < C.gates.length := by omega
  have hjr : j ≠ r := by omega
  have hju := mixedProviderNoResidualUse G C h hl colour hcolour hJ hW hzero hT hsT hdT
    (hcolour s d (hstarA d hd))
  have hjs : W (pairInput s s) (n+j) = true :=
    (hT.2 W hW _).mpr (Or.inl ⟨s,hsT,by simp [pairInput]⟩)
  have hjd : W (pairInput d d) (n+j) = true :=
    (hT.2 W hW _).mpr (Or.inl ⟨d,hdT,by simp [pairInput]⟩)
  have hcharge : ∃ charges : Finset ℕ, j ∉ charges ∧ 1 ≤ charges.card ∧
      (2 ≤ charges.card ∨ W (fun _ => true) C.output = false) ∧
      ∀ t ∈ charges, r < t ∧ t < C.gates.length ∧
        ∃ z ∈ (gateAt C t).inputs, W (fun _ => true) z = false := by
    by_cases hout : W (fun _ => true) C.output = false
    · refine ⟨{i},by simp; omega,by simp,Or.inr hout,?_⟩
      intro t ht
      have he : t = i := Finset.mem_singleton.mp ht
      subst t
      exact ⟨hri,hil,n+r,him,hzero _⟩
    · have hot : W (fun _ => true) C.output = true := by
        cases he : W (fun _ => true) C.output <;> simp_all
      have hz : W (fun _ => true) (n+i) = false := by
        cases he : W (fun _ => true) (n+i)
        · rfl
        · have hh := ((htop W hW _).mp he).1
          rw [hzero] at hh
          cases hh
      have hneout : C.output ≠ n+i := by
        intro he
        rw [he,hz] at hot
        cases hot
      obtain ⟨k,hik,hk,hkm⟩ := noUnreadGate G C h i (n+r) hil
        (h.1.2.1 i hil _ him) hneout
      have hjk : j ≠ k := by omega
      have hji : j ≠ i := by omega
      refine ⟨{i,k},by simp [hji,hjk],by simp [hik.ne],Or.inl (by simp [hik.ne]),?_⟩
      intro t ht
      rcases (show t = i ∨ t = k by simpa using ht) with rfl | rfl
      · exact ⟨hri,hil,n+r,him,hzero _⟩
      · exact ⟨hri.trans hik,hk,n+i,hkm,hz⟩
  obtain ⟨charges,hjn,hcc,hbudget,hch⟩ := hcharge
  exact noOneJunkWithMixedProviderAndTrim G C h hl h4 hJ hab hA hB hdisj hcardA
    hs hd hstarA (fun z hz => (hstarB z hz).symm) hW hzero ⟨u,hu,hmissB⟩ hcover
    hj hjr hwd hju hjs hjd charges hjn hcc hbudget hch

#print axioms noOneJunkAndReader


/-- Two distinct immediate readers pay for any single-star repair.
    Hence both stars must have indispensable noncentral edges. The
    site-specific bypass then excludes the remaining two-OR case. -/
theorem noOneJunkTwoReaders {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    (h4 : NoFourCycle G) (colour : Fin n → Bool)
    (hcolour : ∀ u v, G.Adj u v → colour u ≠ colour v)
    {r i k : ℕ} (hJ : junk G C = {r})
    (hi : i ∈ immediateJunkReaders (n := n) C r)
    (hk : k ∈ immediateJunkReaders (n := n) C r) (hik : i ≠ k) : False := by
  obtain ⟨hil,him⟩ := Finset.mem_filter.mp hi
  obtain ⟨hkl,hkm⟩ := Finset.mem_filter.mp hk
  have hno (j) (hj : j < C.gates.length) (hja : (gateAt C j).op = GateOp.and) :
      n+r ∉ (gateAt C j).inputs := by
    intro hm
    exact noOneJunkAndReader G C h hl h4 colour hcolour hJ
      (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,hm⟩) hja
  have hcount := oneJunkAtMostTwoReaders G C h hl h4 colour hcolour hJ
  obtain ⟨a,b,A,B,s,d,u,v,W,hab,hA,hB,_,hcardA,hcardB,hs,hd,hu,hv,hus,hvd,
    hstarA,hstarB,hW,hzero,hmissB,hmissA,_⟩ :=
    oneJunkNeedsBothStars G C h hl h4 colour hcolour hJ (by
      intro W hW hzero p hp S hS hn c hstar hcover
      exact noOneJunkOneStarWithTwoReaders G C h hl hJ hW hzero
        (Finset.mem_range.mp hil) (Finset.mem_range.mp hkl) hik him hkm hp hS hn c hstar hcover)
  exact noTwoOrReadersBothStars G C h hl h4 colour hcolour hJ hab hno hcount
    hA hB hcardA hcardB hs hd hu hv hus hvd hstarA hstarB hW hzero hmissA hmissB

/-- No minimum exact binary AO edge circuit at a lift fixed point
    has a singleton dirty-AND set. This uses the same pinned upstream
    definitions as the reduction R_meta_3754_1. -/
theorem noLeastOneJunk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : IsLeastAO G C) (hl : IsLiftFixedPoint G C)
    (h4 : NoFourCycle G) (colour : Fin n → Bool)
    (hcolour : ∀ u v, G.Adj u v → colour u ≠ colour v)
    {r : ℕ} (hJ : junk G C = {r}) : False := by
  obtain ⟨hr,hand,hdirty⟩ := junkMember G C hJ
  have hout : C.output ≠ n+r := by
    intro he
    apply hdirty
    intro x hx
    have hf : C.eval (List.ofFn x) = graphFun G ∅ x := congrFun h.2.1 x
    rw [← hf]
    change val C (List.ofFn x) C.output = true
    rw [he]
    change val C (List.ofFn x) (n+r) = true at hx
    exact hx
  obtain ⟨p,q,hpq⟩ := twoOperands h.1 hr
  have hp := h.1.2.1 r hr p (by simp [hpq])
  obtain ⟨i,hri,hi,hir⟩ := noUnreadGate G C h r p hr hp hout
  have hiR : i ∈ immediateJunkReaders (n := n) C r :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi,hir⟩
  have hno (j) (hj : j < C.gates.length) (hja : (gateAt C j).op = GateOp.and) :
      n+r ∉ (gateAt C j).inputs := by
    intro hm
    exact noOneJunkAndReader G C h hl h4 colour hcolour hJ
      (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,hm⟩) hja
  have hio : (gateAt C i).op = GateOp.or := by
    rcases h.1.1 _ (gateAt_mem hi) with ha | ho
    · exact (hno i hi ha hir).elim
    · exact ho
  by_cases hex : ∃ k ∈ immediateJunkReaders (n := n) C r, k ≠ i
  · obtain ⟨k,hk,hki⟩ := hex
    exact noOneJunkTwoReaders G C h hl h4 colour hcolour hJ hiR hk hki.symm
  · have only (j) (hj : j < C.gates.length) (hm : n+r ∈ (gateAt C j).inputs) : j = i := by
      by_contra hn
      exact hex ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,hm⟩,hn⟩
    obtain ⟨a,b,A,B,c,hab,hA,hB,hdisj,hcardA,hcardB,hcolA,hcolB,_⟩ :=
      oneJunkLargeOppositeSupports G C h hl h4 colour hcolour hJ
    exact noSoleOrReaderLargeSupports G C h hl h4 colour hcolour hJ hno hi hio hir only
      hab hA hB hdisj hcardA hcardB c hcolA hcolB

/-- Exact hone hypothesis of upstream reduction R_meta_3754_1.
    In fact its cardinality-one premise is contradictory. -/
theorem oneJunkExact (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) :
    (∀ u v : Fin n, G.Adj u v → s u ≠ s v) →
    NoFourCycle G → IsLeastAO G C → IsLiftFixedPoint G C →
    (junk G C).card = 1 →
    ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → BelowF G C k := by
  intro hbi hC4 hleast hlift hcard k hk hand
  obtain ⟨r,hr⟩ := Finset.card_eq_one.mp hcard
  exact (noLeastOneJunk G C hleast hlift hC4 s hbi hr).elim

#print axioms noOneJunkTwoReaders
#print axioms noLeastOneJunk
#print axioms oneJunkExact

end ResearchVerification.OneJunkErase
