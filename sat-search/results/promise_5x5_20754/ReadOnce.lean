import Mathlib.Data.List.Perm.Basic

namespace Promise20754

abbrev Table := BitVec 12
variable {width : Nat}

inductive Formula (width : Nat) where
  | leaf (value : BitVec width)
  | join (isOr : Bool) (left right : Formula width)

def Formula.leaves : Formula width → List (BitVec width)
  | .leaf v => [v]
  | .join _ left right => left.leaves ++ right.leaves

def Formula.eval : Formula width → BitVec width
  | .leaf v => v
  | .join isOr left right =>
      if isOr then left.eval ||| right.eval else left.eval &&& right.eval

private def splits : List (BitVec width) → List (List (BitVec width) × List (BitVec width))
  | [] => [([], [])]
  | v :: vs => (splits vs).flatMap fun (l, r) => [(v :: l, r), (l, v :: r)]

private theorem splits_complete {xs l r : List (BitVec width)}
    (h : (l ++ r).Perm xs) : ∃ ll rr, (ll, rr) ∈ splits xs ∧ l.Perm ll ∧ r.Perm rr := by
  induction xs generalizing l r with
  | nil =>
    have he : l ++ r = [] := List.perm_nil.mp h
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp he
    exact ⟨[], [], by simp [splits], .refl _, .refl _⟩
  | cons x xs ih =>
    have hm : x ∈ l ++ r := h.mem_iff.mpr (by simp)
    rcases List.mem_append.mp hm with hl | hr
    · let zs := l.erase x
      have hzs : l.Perm (x :: zs) := List.perm_cons_erase hl
      have ht : (zs ++ r).Perm xs := List.Perm.cons_inv ((hzs.append_right r).symm.trans h)
      obtain ⟨ll, rr, hs, hll, hrr⟩ := ih ht
      refine ⟨x :: ll, rr, ?_, hzs.trans (.cons x hll), hrr⟩
      exact List.mem_flatMap.mpr ⟨(ll, rr), hs, by simp⟩
    · let zs := r.erase x
      have hzs : r.Perm (x :: zs) := List.perm_cons_erase hr
      have hp : (l ++ r).Perm (x :: (l ++ zs)) :=
        (hzs.append_left l).trans List.perm_middle
      have ht : (l ++ zs).Perm xs := List.Perm.cons_inv (hp.symm.trans h)
      obtain ⟨ll, rr, hs, hll, hrr⟩ := ih ht
      refine ⟨ll, x :: rr, ?_, hll, hzs.trans (.cons x hrr)⟩
      exact List.mem_flatMap.mpr ⟨(ll, rr), hs, by simp⟩

private def products (ls rs : List (BitVec width)) : List (BitVec width) :=
  ls.flatMap fun l => rs.flatMap fun r => [l &&& r, l ||| r]

private def rawValues (previous : List (BitVec width) → List (BitVec width)) :
    List (BitVec width) → List (BitVec width)
  | [] => []
  | [v] => [v]
  | v :: w :: ws => (splits (v :: w :: ws)).flatMap fun (l, r) =>
      if l.isEmpty || r.isEmpty then [] else products (previous l) (previous r)

def values : Nat → List (BitVec width) → List (BitVec width) :=
  Nat.rec (fun _ => []) fun _ previous xs => (rawValues previous xs).eraseDups

private theorem Formula.leaves_ne_nil (f : Formula width) : f.leaves ≠ [] := by
  induction f with
  | leaf => simp [Formula.leaves]
  | join _ left right ihl ihr => simp [Formula.leaves, ihl]

theorem values_complete (f : Formula width) (xs : List (BitVec width)) (fuel : Nat)
    (hp : f.leaves.Perm xs) (hb : xs.length ≤ fuel) : f.eval ∈ values fuel xs := by
  induction f generalizing xs fuel with
  | leaf v =>
    have hx : xs = [v] := List.perm_singleton.mp hp.symm
    subst xs
    cases fuel <;> simp [values, rawValues, Formula.eval] at *
  | join isOr left right ihl ihr =>
    have hla : 0 < left.leaves.length := by
      cases h : left.leaves with
      | nil => exact (left.leaves_ne_nil h).elim
      | cons => simp
    have hra : 0 < right.leaves.length := by
      cases h : right.leaves with
      | nil => exact (right.leaves_ne_nil h).elim
      | cons => simp
    have hlen : left.leaves.length + right.leaves.length = xs.length := by
      simpa only [Formula.leaves, List.length_append] using hp.length_eq
    rcases fuel with _ | fuel
    · omega
    rcases xs with _ | ⟨v, _ | ⟨w, ws⟩⟩
    · simp only [List.length_nil] at hlen
      omega
    · simp only [List.length_cons, List.length_nil] at hlen
      omega
    obtain ⟨ll, rr, hs, hl, hr⟩ := splits_complete hp
    have hll := hl.length_eq
    have hrr := hr.length_eq
    have hsum : ll.length + rr.length ≤ fuel + 1 := by
      rw [← hll, ← hrr, hlen]
      exact hb
    have hposL : 0 < ll.length := by rwa [← hll]
    have hposR : 0 < rr.length := by rwa [← hrr]
    have hmleft := ihl ll fuel hl (by omega)
    have hmright := ihr rr fuel hr (by omega)
    have hneL : ll ≠ [] := by rintro rfl; simp at hposL
    have hneR : rr ≠ [] := by rintro rfl; simp at hposR
    change _ ∈ (rawValues (values fuel) (v :: w :: ws)).eraseDups
    rw [List.mem_eraseDups, rawValues]
    apply List.mem_flatMap.mpr
    refine ⟨(ll, rr), hs, ?_⟩
    simp only [List.isEmpty_eq_false_iff.mpr hneL, List.isEmpty_eq_false_iff.mpr hneR,
      Bool.false_or, Bool.false_eq_true, reduceIte, products]
    apply List.mem_flatMap.mpr
    refine ⟨left.eval, hmleft, List.mem_flatMap.mpr ⟨right.eval, hmright, ?_⟩⟩
    cases isOr <;> simp [Formula.eval]

def liveInputs : List Table := [15, 240, 3840, 273, 546, 1092, 2184]

def leOn (xs : List Table) (a b : Nat) : Bool :=
  xs.all fun truth => !truth.getLsbD a || truth.getLsbD b

theorem Formula.monotone (f : Formula 12) {xs : List Table} {a b : Nat}
    (hp : f.leaves.Perm xs) (h : leOn xs a b = true) :
    f.eval.getLsbD a = true → f.eval.getLsbD b = true := by
  have hm : ∀ value ∈ f.leaves, value.getLsbD a = true → value.getLsbD b = true := by
    intro value hv ha
    have hh := List.all_eq_true.mp h value (hp.mem_iff.mp hv)
    simpa [ha] using hh
  clear hp h
  induction f with
  | leaf v => exact hm v (by simp [Formula.leaves])
  | join isOr left right ihl ihr =>
    have hleft := ihl (fun v hv => hm v (by simp [Formula.leaves, hv]))
    have hright := ihr (fun v hv => hm v (by simp [Formula.leaves, hv]))
    cases isOr <;> simp only [Formula.eval, Bool.false_eq_true, reduceIte,
      BitVec.getLsbD_and, BitVec.getLsbD_or, Bool.and_eq_true, Bool.or_eq_true] <;> tauto

private def rows : List Nat := List.range 12

private def belowNegative (target : Table) (xs : List Table) (positive : Nat) : Bool :=
  rows.any fun n => !target.getLsbD n && leOn xs positive n

private def abovePositive (target : Table) (xs : List Table) (negative : Nat) : Bool :=
  rows.any fun p => target.getLsbD p && leOn xs p negative

private def orBlocked (target : Table) (left right : List Table) : Bool :=
  rows.any fun p => (target.getLsbD p && belowNegative target left p) && belowNegative target right p

private def andBlocked (target : Table) (left right : List Table) : Bool :=
  rows.any fun n => (!target.getLsbD n && abovePositive target left n) && abovePositive target right n

private theorem orBlocked_sound {target : Table} {ls rs : List Table} {l r : Formula 12}
    (hl : l.leaves.Perm ls) (hr : r.leaves.Perm rs)
    (h : orBlocked target ls rs = true) : (l.eval ||| r.eval) ≠ target := by
  intro eq
  obtain ⟨p, _, hp⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true] at hp
  obtain ⟨⟨hpos, hleft⟩, hright⟩ := hp
  have child {f : Formula 12} {xs : List Table} (perm : f.leaves.Perm xs)
      (below : belowNegative target xs p = true)
      (sub : ∀ n, f.eval.getLsbD n = true → (l.eval ||| r.eval).getLsbD n = true) :
      f.eval.getLsbD p = false := by
    obtain ⟨n, _, hn⟩ := List.any_eq_true.mp below
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hn
    cases hf : f.eval.getLsbD p
    · rfl
    · have contradiction := sub n (f.monotone perm hn.2 hf)
      rw [eq, hn.1] at contradiction
      contradiction
  have h1 := child hl hleft (fun n hn => by simp only [BitVec.getLsbD_or, hn, Bool.true_or])
  have h2 := child hr hright (fun n hn => by simp only [BitVec.getLsbD_or, hn, Bool.or_true])
  rw [← eq, BitVec.getLsbD_or, h1, h2] at hpos
  contradiction

private theorem andBlocked_sound {target : Table} {ls rs : List Table} {l r : Formula 12}
    (hl : l.leaves.Perm ls) (hr : r.leaves.Perm rs)
    (h : andBlocked target ls rs = true) : (l.eval &&& r.eval) ≠ target := by
  intro eq
  obtain ⟨n, _, hn⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hn
  obtain ⟨⟨hneg, hleft⟩, hright⟩ := hn
  have child {f : Formula 12} {xs : List Table} (perm : f.leaves.Perm xs)
      (above : abovePositive target xs n = true)
      (sub : ∀ p, (l.eval &&& r.eval).getLsbD p = true → f.eval.getLsbD p = true) :
      f.eval.getLsbD n = true := by
    obtain ⟨p, _, hp⟩ := List.any_eq_true.mp above
    simp only [Bool.and_eq_true] at hp
    apply f.monotone perm hp.2
    apply sub p
    rw [eq]
    exact hp.1
  have h1 := child hl hleft (fun _ hp => by
    simp only [BitVec.getLsbD_and, Bool.and_eq_true] at hp
    exact hp.1)
  have h2 := child hr hright (fun _ hp => by
    simp only [BitVec.getLsbD_and, Bool.and_eq_true] at hp
    exact hp.2)
  rw [← eq, BitVec.getLsbD_and, h1, h2] at hneg
  contradiction

def allRootsBlocked (target : Table) (xs : List Table) : Bool :=
  (splits xs).all fun (l, r) => l.isEmpty || r.isEmpty || (orBlocked target l r && andBlocked target l r)

theorem blocked_root_excludes {target : Table} {xs : List Table}
    (hlen : 2 ≤ xs.length) (blocked : allRootsBlocked target xs = true)
    (f : Formula 12) (hp : f.leaves.Perm xs) : f.eval ≠ target := by
  cases f with
  | leaf v =>
    have h := hp.length_eq
    simp only [Formula.leaves, List.length_cons, List.length_nil] at h
    omega
  | join isOr left right =>
    obtain ⟨ls, rs, hs, hl, hr⟩ := splits_complete hp
    have hls : ls.isEmpty = false :=
      List.isEmpty_eq_false_iff.mpr (fun eq => left.leaves_ne_nil (List.perm_nil.mp (eq ▸ hl)))
    have hrs : rs.isEmpty = false :=
      List.isEmpty_eq_false_iff.mpr (fun eq => right.leaves_ne_nil (List.perm_nil.mp (eq ▸ hr)))
    have hroot := List.all_eq_true.mp blocked (ls, rs) hs
    change (ls.isEmpty || rs.isEmpty || (orBlocked target ls rs && andBlocked target ls rs)) = true at hroot
    simp only [hls, hrs, Bool.false_or, Bool.and_eq_true] at hroot
    cases isOr
    · exact andBlocked_sound hl hr hroot.2
    · exact orBlocked_sound hl hr hroot.1

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem no_read_once (f : Formula 12) (hp : f.leaves.Perm liveInputs) : f.eval ≠ 3187 := by
  exact blocked_root_excludes (by decide) (by decide +kernel) f hp

def Matches (table : Table) (bit : Bool) (rs : List Nat) : Prop :=
  ∀ row ∈ rs, table.getLsbD row = bit

private def allowable (xs : List Table) (bit : Bool) (shared : List Nat) (row : Nat) : Bool :=
  !(shared.any fun other => if bit then leOn xs row other else leOn xs other row)

private theorem allowable_of_matches (f : Formula 12) {xs : List Table} (perm : f.leaves.Perm xs)
    {bit : Bool} {shared : List Nat} {row : Nat}
    (common : Matches f.eval (!bit) shared) (atRow : f.eval.getLsbD row = bit) :
    allowable xs bit shared row = true := by
  unfold allowable
  rw [Bool.not_eq_true']
  cases h : shared.any _ with
  | false => rfl
  | true =>
    obtain ⟨other, ho, order⟩ := List.any_eq_true.mp h
    have opposite := common other ho
    cases bit
    · simp only [Bool.false_eq_true, reduceIte] at order
      have wrong := f.monotone perm order opposite
      rw [atRow] at wrong
      contradiction
    · simp only [reduceIte] at order
      have wrong := f.monotone perm order atRow
      rw [opposite] at wrong
      contradiction

private def allocations (a b : Nat → Bool) : List Nat → List (List Nat × List Nat)
  | [] => [([], [])]
  | row :: rest => (allocations a b rest).flatMap fun (l, r) =>
      (if a row then [(row :: l, r)] else []) ++ (if b row then [(l, row :: r)] else [])

private theorem allocations_complete (a b : Nat → Bool) (pl pr : Nat → Prop) (rs : List Nat)
    (h : ∀ i ∈ rs, (a i = true ∧ pl i) ∨ (b i = true ∧ pr i)) :
    ∃ l r, (l, r) ∈ allocations a b rs ∧ (∀ i ∈ l, pl i) ∧ (∀ i ∈ r, pr i) := by
  induction rs with
  | nil => exact ⟨[], [], by simp [allocations], by simp, by simp⟩
  | cons i rest ih =>
    obtain ⟨l, r, hm, hl, hr⟩ := ih (fun j hj => h j (by simp [hj]))
    rcases h i (by simp) with ⟨ha, hp⟩ | ⟨hb, hp⟩
    · refine ⟨i :: l, r, List.mem_flatMap.mpr ⟨(l, r), hm, ?_⟩, ?_, hr⟩
      · simp [ha]
      · intro j hj
        rcases List.mem_cons.mp hj with rfl | hj
        · exact hp
        · exact hl j hj
    · refine ⟨l, i :: r, List.mem_flatMap.mpr ⟨(l, r), hm, ?_⟩, hl, ?_⟩
      · simp [hb]
      · intro j hj
        rcases List.mem_cons.mp hj with rfl | hj
        · exact hp
        · exact hr j hj

private abbrev Search := List Table → List Nat → List Nat → Bool

private def tryJoin (previous : Search) (isOr : Bool) (ls rs : List Table)
    (on off : List Nat) : Bool :=
  let shared := if isOr then off else on
  let split := if isOr then on else off
  (allocations (allowable ls isOr shared) (allowable rs isOr shared) split).any fun (l, r) =>
    if isOr then previous ls l shared && previous rs r shared
    else previous ls shared l && previous rs shared r

def canMatch : Nat → Search :=
  Nat.rec (fun _ _ _ => false) fun _ previous xs on off =>
    match xs with
    | [] => false
    | [v] => (on.all v.getLsbD) && (off.all fun i => !v.getLsbD i)
    | l :: r :: more =>
      (splits (l :: r :: more)).any fun (ls, rs) =>
        if ls.isEmpty || rs.isEmpty then false else
          tryJoin previous true ls rs on off || tryJoin previous false ls rs on off

private theorem tryJoin_complete (previous : Search) (isOr : Bool)
    {ls rs : List Table} {l r : Formula 12} {on off : List Nat}
    (hl : l.leaves.Perm ls) (hr : r.leaves.Perm rs)
    (leftOk : ∀ p n, Matches l.eval true p → Matches l.eval false n → previous ls p n = true)
    (rightOk : ∀ p n, Matches r.eval true p → Matches r.eval false n → previous rs p n = true)
    (hon : Matches (Formula.join isOr l r).eval true on)
    (hoff : Matches (Formula.join isOr l r).eval false off) :
    tryJoin previous isOr ls rs on off = true := by
  let shared := if isOr then off else on
  let split := if isOr then on else off
  have hshared : (Matches l.eval (!isOr) shared) ∧ (Matches r.eval (!isOr) shared) := by
    cases isOr
    · constructor <;> intro i hi <;>
        have h := hon i hi <;>
        simp only [Formula.eval, Bool.false_eq_true, reduceIte,
          BitVec.getLsbD_and, Bool.and_eq_true] at h
      · exact h.1
      · exact h.2
    · constructor <;> intro i hi <;>
        have h := hoff i hi <;>
        simp only [Formula.eval, reduceIte, BitVec.getLsbD_or, Bool.or_eq_false_iff] at h
      · exact h.1
      · exact h.2
  have hsplit : ∀ i ∈ split, l.eval.getLsbD i = isOr ∨ r.eval.getLsbD i = isOr := by
    intro i hi
    cases isOr
    · have h := hoff i hi
      simpa only [Formula.eval, Bool.false_eq_true, reduceIte,
        BitVec.getLsbD_and, Bool.and_eq_false_iff] using h
    · have h := hon i hi
      simpa only [Formula.eval, reduceIte, BitVec.getLsbD_or, Bool.or_eq_true] using h
  obtain ⟨p, q, hm, hp, hq⟩ := allocations_complete (allowable ls isOr shared)
    (allowable rs isOr shared) (fun i => l.eval.getLsbD i = isOr)
    (fun i => r.eval.getLsbD i = isOr) split (fun i hi =>
      (hsplit i hi).imp (fun h => ⟨allowable_of_matches l hl hshared.1 h, h⟩)
        (fun h => ⟨allowable_of_matches r hr hshared.2 h, h⟩))
  apply List.any_eq_true.mpr
  refine ⟨(p, q), hm, ?_⟩
  cases isOr
  · change (previous ls on p && previous rs on q) = true
    simp only [leftOk on p hshared.1 hp, rightOk on q hshared.2 hq, Bool.and_self]
  · change (previous ls p off && previous rs q off) = true
    simp only [leftOk p off hp hshared.1, rightOk q off hq hshared.2, Bool.and_self]

theorem canMatch_complete (f : Formula 12) (xs : List Table) (fuel : Nat) (on off : List Nat)
    (perm : f.leaves.Perm xs) (budget : xs.length ≤ fuel)
    (hon : Matches f.eval true on) (hoff : Matches f.eval false off) :
    canMatch fuel xs on off = true := by
  induction f generalizing xs fuel on off with
  | leaf v =>
    have hx : xs = [v] := List.perm_singleton.mp perm.symm
    subst xs
    cases fuel with
    | zero => simp at budget
    | succ n =>
      change (on.all v.getLsbD && off.all (fun i => !v.getLsbD i)) = true
      simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true']
      exact ⟨hon, hoff⟩
  | join isOr l r ihl ihr =>
    have hlen : l.leaves.length + r.leaves.length = xs.length := by
      simpa only [Formula.leaves, List.length_append] using perm.length_eq
    have hposL : 0 < l.leaves.length := Nat.pos_of_ne_zero (fun h => l.leaves_ne_nil (List.length_eq_zero_iff.mp h))
    have hposR : 0 < r.leaves.length := Nat.pos_of_ne_zero (fun h => r.leaves_ne_nil (List.length_eq_zero_iff.mp h))
    rcases fuel with _ | fuel
    · omega
    rcases xs with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · simp only [List.length_nil] at hlen
      omega
    · simp only [List.length_cons, List.length_nil] at hlen
      omega
    obtain ⟨ls, rs, hs, hl, hr⟩ := splits_complete perm
    have hsum : ls.length + rs.length ≤ fuel + 1 := by
      rw [← hl.length_eq, ← hr.length_eq, hlen]
      exact budget
    have hlo : 0 < ls.length := by rwa [← hl.length_eq]
    have hro : 0 < rs.length := by rwa [← hr.length_eq]
    have hls : ls.isEmpty = false := List.isEmpty_eq_false_iff.mpr (by rintro rfl; simp at hlo)
    have hrs : rs.isEmpty = false := List.isEmpty_eq_false_iff.mpr (by rintro rfl; simp at hro)
    have hj := tryJoin_complete (canMatch fuel) isOr hl hr
      (fun p n => ihl ls fuel p n hl (by omega)) (fun p n => ihr rs fuel p n hr (by omega)) hon hoff
    change ((splits (a :: b :: rest)).any fun (ls, rs) =>
      if ls.isEmpty || rs.isEmpty then false else
        tryJoin (canMatch fuel) true ls rs on off || tryJoin (canMatch fuel) false ls rs on off) = true
    apply List.any_eq_true.mpr
    refine ⟨(ls, rs), hs, ?_⟩
    simp only [hls, hrs, Bool.false_or, Bool.false_eq_true, reduceIte, Bool.or_eq_true]
    cases isOr
    · exact Or.inr hj
    · exact Or.inl hj

private def wantedRows (target : Table) (value : Bool) : List Nat :=
  rows.filter (fun i => target.getLsbD i == value)

private theorem target_matches (t : Table) (v : Bool) : Matches t v (wantedRows t v) := by
  intro i hi
  exact beq_iff_eq.mp (List.mem_filter.mp hi).2

private theorem force_module {target m : Table} {outside : List Table} {outer : Formula 12}
    (hp : outer.leaves.Perm (m :: m :: outside)) (eq : outer.eval = target)
    {a b : Nat} (ha : target.getLsbD a = true) (hb : target.getLsbD b = false)
    (order : leOn outside a b = true) : m.getLsbD a = true ∧ m.getLsbD b = false := by
  have h : ¬ ((!m.getLsbD a || m.getLsbD b) = true) := by
    intro morder
    have whole : leOn (m :: m :: outside) a b = true := by
      simp only [leOn, List.all_cons] at *
      simp only [morder, order, Bool.true_and]
    have impossible := outer.monotone hp whole (eq ▸ ha)
    rw [eq, hb] at impossible
    contradiction
  cases h₁ : m.getLsbD a <;> cases h₂ : m.getLsbD b <;> simp_all

private def forcedOn (target : Table) (outside : List Table) : List Nat :=
  (wantedRows target true).filter (belowNegative target outside)

private def forcedOff (target : Table) (outside : List Table) : List Nat :=
  (wantedRows target false).filter (abovePositive target outside)

private theorem module_matches {target m : Table} {outside : List Table} {outer : Formula 12}
    (hp : outer.leaves.Perm (m :: m :: outside)) (eq : outer.eval = target) :
    Matches m true (forcedOn target outside) ∧ Matches m false (forcedOff target outside) := by
  constructor
  · intro a ha
    obtain ⟨ha, hb⟩ := List.mem_filter.mp ha
    obtain ⟨b, _, hh⟩ := List.any_eq_true.mp hb
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hh
    exact (force_module hp eq (target_matches target true a ha) hh.1 hh.2).1
  · intro b hb
    obtain ⟨hb, ha⟩ := List.mem_filter.mp hb
    obtain ⟨a, _, hh⟩ := List.any_eq_true.mp ha
    simp only [Bool.and_eq_true] at hh
    exact (force_module hp eq hh.1 (target_matches target false b hb) hh.2).2

private def contradicts (xs : List Table) (on off : List Nat) : Bool :=
  on.any fun a => off.any fun b => leOn xs a b

private theorem no_conflict {f : Formula 12} {xs : List Table} {on off : List Nat}
    (hp : f.leaves.Perm xs) (ho : Matches f.eval true on) (hn : Matches f.eval false off) :
    contradicts xs on off = false := by
  cases hc : contradicts xs on off
  · rfl
  · obtain ⟨a, ha, hh⟩ := List.any_eq_true.mp hc
    obtain ⟨b, hb, hh⟩ := List.any_eq_true.mp hh
    have wrong := f.monotone hp hh (ho a ha)
    rw [hn b hb] at wrong
    contradiction

private def properCandidates (target : Table) (xs : List Table) : List (Table × List Table) :=
  (splits xs).flatMap fun (inner, outside) =>
    let on := forcedOn target outside
    let off := forcedOff target outside
    if outside.isEmpty || contradicts inner on off then [] else
      ((values inner.length inner).filter fun m =>
        (on.all m.getLsbD) && (off.all fun i => !m.getLsbD i)).map fun m => (m, outside)

private theorem proper_candidate {target : Table} {xs ins outside : List Table}
    {inner outer : Formula 12}
    (full : (ins ++ outside).Perm xs) (nn : outside ≠ []) (mi : inner.leaves.Perm ins)
    (mo : outer.leaves.Perm (inner.eval :: inner.eval :: outside)) (eq : outer.eval = target) :
    ∃ ext, (inner.eval, ext) ∈ properCandidates target xs ∧
      outer.leaves.Perm (inner.eval :: inner.eval :: ext) := by
  obtain ⟨ls, rs, hs, hl, hr⟩ := splits_complete full
  have ip := mi.trans hl
  have op := mo.trans (.cons _ (.cons _ hr))
  have hn : rs.isEmpty = false :=
    List.isEmpty_eq_false_iff.mpr (fun h => nn (List.perm_nil.mp (h ▸ hr)))
  obtain ⟨hon, hoff⟩ := module_matches op eq
  have hc := no_conflict ip hon hoff
  refine ⟨rs, List.mem_flatMap.mpr ⟨(ls, rs), hs, ?_⟩, op⟩
  simp only [hn, hc, Bool.false_or, Bool.false_eq_true, reduceIte]
  apply List.mem_map.mpr
  refine ⟨inner.eval, List.mem_filter.mpr ⟨values_complete inner ls ls.length ip (Nat.le_refl _), ?_⟩, rfl⟩
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true']
  exact ⟨hon, hoff⟩

private theorem constant_leaves {f : Formula 12} {value : Table}
    (h : ∀ v ∈ f.leaves, v = value) : f.eval = value := by
  induction f with
  | leaf v => exact h v (by simp [Formula.leaves])
  | join op l r ihl ihr =>
    have hl := ihl (fun v hv => h v (by simp [Formula.leaves, hv]))
    have hr := ihr (fun v hv => h v (by simp [Formula.leaves, hv]))
    simp [Formula.eval, hl, hr]

private def canMatchTarget (target : Table) (c : Table × List Table) : Bool :=
  canMatch (c.2.length + 2) (c.1 :: c.1 :: c.2) (wantedRows target true) (wantedRows target false)

theorem no_once_shared_of_check {target : Table} {xs ins outside : List Table}
    {inner outer : Formula 12}
    (noOrdinary : ∀ f : Formula 12, f.leaves.Perm xs → f.eval ≠ target)
    (check : ((properCandidates target xs).any (canMatchTarget target)) = false)
    (full : (ins ++ outside).Perm xs) (mi : inner.leaves.Perm ins)
    (mo : outer.leaves.Perm (inner.eval :: inner.eval :: outside)) :
    outer.eval ≠ target := by
  intro eq
  by_cases nn : outside = []
  · subst outside
    have he := constant_leaves (f := outer) (value := inner.eval) (fun v hv => by
      simpa using mo.mem_iff.mp hv)
    exact noOrdinary inner (mi.trans (by simpa using full)) (he.symm.trans eq)
  · obtain ⟨ext, hc, hp⟩ := proper_candidate full nn mi mo eq
    have ok : canMatchTarget target (inner.eval, ext) = true := by
      apply canMatch_complete outer _ _ _ _ hp (by simp)
      · rw [eq]
        exact target_matches target true
      · rw [eq]
        exact target_matches target false
    have wrong := List.any_eq_true.mpr ⟨(inner.eval, ext), hc, ok⟩
    rw [check] at wrong
    contradiction

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem no_once_shared {ins outside : List Table} {inner outer : Formula 12}
    (full : (ins ++ outside).Perm liveInputs) (mi : inner.leaves.Perm ins)
    (mo : outer.leaves.Perm (inner.eval :: inner.eval :: outside)) :
    outer.eval ≠ 3187 :=
  no_once_shared_of_check no_read_once (by decide +kernel) full mi mo

private def without (v : Table) (xs : List Table) : List Table :=
  xs.filter (· != v)

private def distinguishes (target : Table) (xs : List Table) (v : Table) : Bool :=
  (wantedRows target true).any fun p =>
    (wantedRows target false).any fun n => leOn (without v xs) p n

theorem input_required_of_dominance {pending : List Table}
    (support : ∀ v ∈ pending, v ∈ liveInputs ++ [0, 4095])
    (respects : ∀ p n, leOn pending p n = true →
      (3187 : Table).getLsbD p = true → (3187 : Table).getLsbD n = true)
    {source : Table} (hm : source ∈ liveInputs) : source ∈ pending := by
  have separated : liveInputs.all (distinguishes 3187 (liveInputs ++ [0, 4095])) = true := by
    decide +kernel
  obtain ⟨p, hp, hn⟩ := List.any_eq_true.mp (List.all_eq_true.mp separated source hm)
  obtain ⟨n, hn, hd⟩ := List.any_eq_true.mp hn
  by_contra dropped
  have le : leOn pending p n = true := by
    apply List.all_eq_true.mpr
    intro v hv
    apply List.all_eq_true.mp hd v
    apply List.mem_filter.mpr
    exact ⟨support v hv, by simpa using (show v ≠ source from fun he => dropped (he ▸ hv))⟩
  have wrong := respects p n le (target_matches 3187 true p hp)
  rw [target_matches 3187 false n hn] at wrong
  contradiction

theorem input_required {f : Formula 12} (eq : f.eval = 3187)
    (support : ∀ v ∈ f.leaves, v ∈ liveInputs ++ [0, 4095])
    {source : Table} (hm : source ∈ liveInputs) : source ∈ f.leaves := by
  apply input_required_of_dominance support _ hm
  intro p n hp
  rw [← eq]
  exact f.monotone (.refl _) hp

end Promise20754
