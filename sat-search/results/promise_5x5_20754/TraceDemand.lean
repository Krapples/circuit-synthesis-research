import ReadOnce
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Perm.Subperm

namespace Promise20754

structure Rule where
  isOr : Bool
  left : Table
  right : Table

def Rule.result (r : Rule) : Table :=
  if r.isOr then r.left ||| r.right else r.left &&& r.right

def bases : List Table := liveInputs ++ [0, 4095]

def available (rs : List Rule) : List Table := rs.map Rule.result ++ bases

inductive CorrectTrace : List Rule → Prop where
  | empty : CorrectTrace []
  | add (r : Rule) (rs : List Rule) :
      CorrectTrace rs → r.left ∈ available rs → r.right ∈ available rs →
      r.result ∉ available rs → CorrectTrace (r :: rs)

def before (r : Rule) (uses : List Table) : List Table :=
  if r.result ∈ uses then r.left :: r.right :: uses.filter (· != r.result) else uses

def cost (r : Rule) (uses : List Table) : Nat :=
  if r.result ∈ uses then uses.count r.result - 1 else 1

def pending : List Rule → List Table → List Table
  | [], uses => uses
  | r :: rs, uses => pending rs (before r uses)

def totalCost : List Rule → List Table → Nat
  | [], _ => 0
  | r :: rs, uses => cost r uses + totalCost rs (before r uses)

private theorem before_length (r : Rule) (uses : List Table) :
    (before r uses).length + cost r uses = uses.length + 1 := by
  by_cases used : r.result ∈ uses
  · have hcount : 0 < uses.count r.result := List.count_pos_iff.mpr used
    have hfilter : uses.length = uses.count r.result + (uses.filter (· != r.result)).length := by
      rw [List.count_eq_length_filter, ← List.countP_eq_length_filter,
        ← List.countP_eq_length_filter]
      exact List.length_eq_countP_add_countP (· == r.result)
    simp only [before, cost, ite_eq_left used, List.length_cons]
    omega
  · simp [before, cost, used]

theorem totalCost_eq (rs : List Rule) (uses : List Table) :
    (pending rs uses).length + totalCost rs uses = uses.length + rs.length := by
  induction rs generalizing uses with
  | nil => simp [pending, totalCost]
  | cons r rs ih =>
    have hfirst := before_length r uses
    have hrest := ih (before r uses)
    simp only [pending, totalCost, List.length_cons]
    omega

private theorem before_available {r : Rule} {rs : List Rule} {uses : List Table}
    (left : r.left ∈ available rs) (right : r.right ∈ available rs)
    (valid : ∀ v ∈ uses, v ∈ available (r :: rs)) :
    ∀ v ∈ before r uses, v ∈ available rs := by
  intro v hv
  have old (mem : v ∈ uses) (ne : v ≠ r.result) : v ∈ available rs := by
    have hm := valid v mem
    change v ∈ r.result :: available rs at hm
    exact (List.mem_cons.mp hm).resolve_left ne
  by_cases used : r.result ∈ uses
  · simp only [before, ite_eq_left used, List.mem_cons, List.mem_filter] at hv
    rcases hv with rfl | rfl | ⟨hm, hn⟩
    · exact left
    · exact right
    · exact old hm (by simpa using hn)
  · rw [before, ite_eq_right used] at hv
    exact old hv (fun eq => used (eq ▸ hv))

theorem pending_available {rs : List Rule} (trace : CorrectTrace rs) {uses : List Table}
    (valid : ∀ v ∈ uses, v ∈ available rs) : ∀ v ∈ pending rs uses, v ∈ bases := by
  induction trace generalizing uses with
  | empty => exact valid
  | add r rs _ hl hr _ ih => exact ih (before_available hl hr valid)

private theorem result_order (r : Rule) (p n : Nat)
    (hl : (!r.left.getLsbD p || r.left.getLsbD n) = true)
    (hr : (!r.right.getLsbD p || r.right.getLsbD n) = true) :
    (!r.result.getLsbD p || r.result.getLsbD n) = true := by
  obtain ⟨isOr, l, rr⟩ := r
  cases hlp : l.getLsbD p <;> cases hln : l.getLsbD n <;>
    cases hrp : rr.getLsbD p <;> cases hrn : rr.getLsbD n <;>
    cases isOr <;> simp_all [Rule.result, BitVec.getLsbD_and, BitVec.getLsbD_or]

private theorem before_order (r : Rule) (uses : List Table) (p n : Nat)
    (h : leOn (before r uses) p n = true) : leOn uses p n = true := by
  by_cases used : r.result ∈ uses
  · rw [before, ite_eq_left used] at h
    apply List.all_eq_true.mpr
    intro v hv
    have all := List.all_eq_true.mp h
    by_cases ve : v = r.result
    · subst v
      exact result_order r p n (all _ (by simp)) (all _ (by simp))
    · exact all v (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_filter.mpr ⟨hv, by simpa using ve⟩)))
  · rwa [before, ite_eq_right used] at h

theorem pending_order (rs : List Rule) (uses : List Table) (p n : Nat)
    (h : leOn (pending rs uses) p n = true) : leOn uses p n = true := by
  induction rs generalizing uses with
  | nil => exact h
  | cons r rs ih => exact before_order r uses p n (ih _ h)

theorem mandatory_inputs {rs : List Rule} (trace : CorrectTrace rs)
    (root : 3187 ∈ available rs) : liveInputs ⊆ pending rs [3187] := by
  intro v hv
  have support := pending_available trace (uses := [3187]) (fun v hv => by
    simpa only [List.mem_singleton.mp hv] using root)
  apply input_required_of_dominance support _ hv
  intro p n h hp
  have hh := pending_order rs [3187] p n h
  have hn := List.all_eq_true.mp hh (3187 : Table) (by simp)
  change (!((3187 : Table).getLsbD p) || (3187 : Table).getLsbD n) = true at hn
  rw [hp] at hn
  exact hn

theorem at_most_one_nonordinary_read {rs : List Rule} (trace : CorrectTrace rs)
    (root : 3187 ∈ available rs) (limit : rs.length ≤ 7) :
    totalCost rs [3187] ≤ 1 ∧ (pending rs [3187]).length ≤ 8 := by
  have hnodup : liveInputs.Nodup := by decide
  have hmin : 7 ≤ (pending rs [3187]).length :=
    hnodup.length_le_of_subset (mandatory_inputs trace root)
  have hsum := totalCost_eq rs [3187]
  simp only [List.length_cons, List.length_nil, Nat.zero_add] at hsum
  omega

private def dropValue (m : Table) (uses : List Table) : List Table :=
  uses.filter (· != m)

private theorem extract_count (uses : List Table) (m : Table) :
    (List.replicate (uses.count m) m ++ dropValue m uses).Perm uses := by
  rw [← List.filter_beq]
  exact List.filter_append_perm (· == m) uses

private def expansion (r : Rule) : Formula 12 :=
  .join r.isOr (.leaf r.left) (.leaf r.right)

private def expand (r : Rule) : Formula 12 → Formula 12
  | .leaf v => if v = r.result then expansion r else .leaf v
  | .join op a b => .join op (expand r a) (expand r b)

private theorem expand_eval (r : Rule) (f : Formula 12) : (expand r f).eval = f.eval := by
  induction f with
  | leaf v =>
    by_cases h : v = r.result
    · simp [expand, expansion, Formula.eval, h, Rule.result]
    · simp [expand, Formula.eval, h]
  | join op a b ia ib => simp [expand, Formula.eval, ia, ib]

private def expandList (r : Rule) (v : Table) : List Table :=
  if v = r.result then [r.left, r.right] else [v]

private theorem expand_leaves (r : Rule) (f : Formula 12) :
    (expand r f).leaves = f.leaves.flatMap (expandList r) := by
  induction f with
  | leaf v =>
    by_cases h : v = r.result <;> simp [expand, expansion, Formula.leaves, expandList, h]
  | join op a b ia ib => simp [expand, Formula.leaves, List.flatMap_append, ia, ib]

private theorem flatMap_omit (r : Rule) (uses : List Table) :
    (dropValue r.result uses).flatMap (expandList r) = dropValue r.result uses := by
  calc
    _ = (dropValue r.result uses).flatMap (fun v => [v]) := by
      apply List.flatMap_congr
      intro v hv
      have ne : v ≠ r.result := by
        simpa using (List.mem_filter.mp hv).2
      simp [expandList, ne]
    _ = _ := List.flatMap_singleton' _

private theorem inline_one (r : Rule) (uses : List Table) (count : uses.count r.result = 1) :
    (uses.flatMap (expandList r)).Perm (before r uses) := by
  have used : r.result ∈ uses := List.count_pos_iff.mp (by omega)
  have gather := extract_count uses r.result
  rw [count] at gather
  have flat := gather.symm.flatMap_right (expandList r)
  change (uses.flatMap (expandList r)).Perm
    ((expandList r r.result) ++ (dropValue r.result uses).flatMap (expandList r)) at flat
  rw [flatMap_omit] at flat
  simpa [before, used, expandList, dropValue] using flat

private theorem expand_no_new_marker (r : Rule) (f : Formula 12) (m : Table)
    (hl : m ≠ r.left) (hr : m ≠ r.right) (hm : m ∉ f.leaves) : m ∉ (expand r f).leaves := by
  rw [expand_leaves]
  intro has
  obtain ⟨v, hv, hi⟩ := List.mem_flatMap.mp has
  by_cases h : v = r.result
  · simp [expandList, h, hl, hr] at hi
  · have eq : m = v := by simpa [expandList, h] using hi
    exact hm (eq ▸ hv)

private theorem paired_step {r : Rule} {uses : List Table} {outer inner : Formula 12}
    {marker : Table} (hne : marker ≠ r.result) (count : uses.count r.result = 1)
    (perm : (outer.leaves ++ inner.leaves).Perm (marker :: marker :: uses)) :
    ((expand r outer).leaves ++ (expand r inner).leaves).Perm (marker :: marker :: before r uses) := by
  rw [expand_leaves, expand_leaves, ← List.flatMap_append]
  have mapped := perm.flatMap_right (expandList r)
  have shifted : ((marker :: marker :: uses).flatMap (expandList r)).Perm
      (marker :: marker :: before r uses) := by
    simpa [expandList, hne] using ((inline_one r uses count).cons marker).cons marker
  exact mapped.trans shifted

private theorem zero_usage {r : Rule} {uses : List Table} (h : cost r uses = 0) :
    uses.count r.result = 1 := by
  by_cases used : r.result ∈ uses
  · have order := List.count_pos_iff.mpr used
    simp only [cost, ite_eq_left used] at h
    omega
  · simp [cost, used] at h

private theorem paired_walk {rs : List Rule} (trace : CorrectTrace rs)
    (marker : Table) (unavailable : marker ∉ available rs) (uses : List Table)
    (outer inner : Formula 12)
    (perm : (outer.leaves ++ inner.leaves).Perm (marker :: marker :: uses))
    (outside : marker ∉ inner.leaves)
    (charge : totalCost rs uses = 0) :
    ∃ ofn ifn : Formula 12, ofn.eval = outer.eval ∧ ifn.eval = inner.eval ∧
      (ofn.leaves ++ ifn.leaves).Perm (marker :: marker :: pending rs uses) ∧ marker ∉ ifn.leaves := by
  induction trace generalizing uses outer inner with
  | empty => exact ⟨outer, inner, rfl, rfl, perm, outside⟩
  | add r rs _ hl hr _ ih =>
    have smaller : marker ∉ available rs := by
      intro h
      exact unavailable (List.mem_cons_of_mem _ h)
    have diff : marker ≠ r.result := fun eq => unavailable (eq ▸ List.mem_cons_self)
    have h0 : cost r uses = 0 := by
      simp only [totalCost] at charge
      omega
    have finished : totalCost rs (before r uses) = 0 := by
      simp only [totalCost] at charge
      omega
    have noMarker := expand_no_new_marker r inner marker
      (fun eq => smaller (eq ▸ hl)) (fun eq => smaller (eq ▸ hr)) outside
    obtain ⟨f, g, ef, eg, hperm, hnone⟩ := ih smaller (before r uses) (expand r outer)
      (expand r inner) (paired_step diff (zero_usage h0) perm) noMarker finished
    exact ⟨f, g, ef.trans (expand_eval r outer), eg.trans (expand_eval r inner), hperm, hnone⟩

inductive Shape (target : Table) (uses : List Table) (spent : Nat) : Prop where
  | single (f : Formula 12) : f.eval = target → f.leaves.Perm uses → Shape target uses spent
  | paired (outer inner : Formula 12) (outside : List Table) :
      outer.eval = target → outer.leaves.Perm (inner.eval :: inner.eval :: outside) →
      (inner.leaves ++ outside).Perm uses → 0 < spent → Shape target uses spent

private theorem Shape.weaken {t : Table} {uses : List Table} {a b : Nat}
    (h : Shape t uses a) (hb : a ≤ b) : Shape t uses b := by
  cases h with
  | single f he hp => exact .single f he hp
  | paired outer inner outside he hp hleaves hpos =>
    exact .paired outer inner outside he hp hleaves (by omega)

private theorem finish_pair {target marker : Table} {uses : List Table} {outer inner : Formula 12} {spent : Nat}
    (he : outer.eval = target) (hm : inner.eval = marker)
    (hp : (outer.leaves ++ inner.leaves).Perm (marker :: marker :: uses))
    (hn : marker ∉ inner.leaves) (hUses : marker ∉ uses) (hspent : 0 < spent) :
    Shape target uses spent := by
  have count := hp.count_eq marker
  rw [List.count_append, List.count_eq_zero_of_not_mem hn, Nat.add_zero] at count
  have countUses := List.count_eq_zero_of_not_mem hUses
  have outerCount : outer.leaves.count marker = 2 := by
    simpa [countUses] using count
  have outside := extract_count outer.leaves marker
  rw [outerCount] at outside
  have opp : outer.leaves.Perm (marker :: marker :: dropValue marker outer.leaves) := outside.symm
  have tail := (opp.append_right inner.leaves).symm.trans hp
  have realLeaves : (dropValue marker outer.leaves ++ inner.leaves).Perm uses :=
    List.Perm.cons_inv (List.Perm.cons_inv tail)
  have outerLeaves : outer.leaves.Perm (inner.eval :: inner.eval :: dropValue marker outer.leaves) := by
    rw [hm]
    exact opp
  exact .paired outer inner _ he outerLeaves (List.perm_append_comm.trans realLeaves) hspent

theorem shape_of_cost {rs : List Rule} (trace : CorrectTrace rs) (uses : List Table) (f : Formula 12)
    (hp : f.leaves.Perm uses) (valid : ∀ v ∈ uses, v ∈ available rs) (charge : totalCost rs uses ≤ 1) :
    Shape f.eval (pending rs uses) (totalCost rs uses) := by
  induction trace generalizing uses f with
  | empty => exact .single f rfl hp
  | add r rs trace hl hr fresh ih =>
    have nextValid := before_available hl hr valid
    by_cases used : r.result ∈ uses
    · have count : 0 < uses.count r.result := List.count_pos_iff.mpr used
      have oneOrTwo : uses.count r.result = 1 ∨ uses.count r.result = 2 := by
        simp only [totalCost, cost, ite_eq_left used] at charge
        omega
      rcases oneOrTwo with one | two
      · have hstep := (hp.flatMap_right (expandList r)).trans (inline_one r uses one)
        rw [← expand_leaves] at hstep
        have hshape := ih (before r uses) (expand r f) hstep nextValid
          (by simp only [totalCost] at charge; omega)
        rw [expand_eval] at hshape
        exact hshape.weaken (by simp only [totalCost]; omega)
      · have zero : totalCost rs (before r uses) = 0 := by
          simp only [totalCost, cost, ite_eq_left used, two] at charge
          omega
        have block := (hp.trans (extract_count uses r.result).symm)
        rw [two] at block
        have heavy : (f.leaves ++ (expansion r).leaves).Perm
            (r.result :: r.result :: before r uses) := by
          have old := block.append_right (expansion r).leaves
          rw [before, ite_eq_left used]
          exact old.trans (((List.perm_append_comm (l₁ := dropValue r.result uses)
            (l₂ := [r.left, r.right])).cons r.result).cons r.result)
        have no : r.result ∉ (expansion r).leaves := by
          intro h
          simp only [expansion, Formula.leaves, List.cons_append, List.nil_append,
            List.mem_cons, List.not_mem_nil, or_false] at h
          exact fresh (h.elim (fun e => e ▸ hl) (fun e => e ▸ hr))
        obtain ⟨outer, inner, ho, hi, hperm, hnone⟩ := paired_walk trace r.result fresh
          (before r uses) f (expansion r) heavy no zero
        have hUses : r.result ∉ pending rs (before r uses) := by
          intro hk
          have base := pending_available trace nextValid r.result hk
          exact fresh (List.mem_append.mpr (Or.inr base))
        exact finish_pair ho hi hperm hnone hUses (by
          simp only [totalCost, cost, ite_eq_left used, two]
          omega)
    · have hcharge : totalCost rs uses ≤ 1 := by
        simp only [totalCost, cost, before, ite_eq_right used] at charge
        omega
      rw [before, ite_eq_right used] at nextValid
      have h := ih uses f hp nextValid hcharge
      have hh := h.weaken (b := cost r uses + totalCost rs uses) (by omega)
      simpa only [pending, totalCost, before, ite_eq_right used] using hh

private abbrev Reduced := Bool ⊕ Formula 12

private def Reduced.value : Reduced → Table
  | .inl false => 0#12
  | .inl true => BitVec.allOnes 12
  | .inr f => f.eval

private def Reduced.leaves : Reduced → List Table
  | .inl _ => []
  | .inr f => f.leaves

private def reducedJoin (op : Bool) (a b : Reduced) : Reduced :=
  match a, b with
  | .inl v, .inl w => .inl (if op then v || w else v && w)
  | .inl v, .inr f | .inr f, .inl v => if v = op then .inl v else .inr f
  | .inr f, .inr g => .inr (.join op f g)

private theorem reducedJoin_value (op : Bool) (a b : Reduced) :
    (reducedJoin op a b).value = (if op then a.value ||| b.value else a.value &&& b.value) := by
  rcases a with (_ | _) | f <;> rcases b with (_ | _) | g <;> cases op <;>
    simp only [reducedJoin, Reduced.value, Formula.eval, Bool.false_eq_true, Bool.true_eq_false,
      reduceIte, Bool.and, Bool.or, BitVec.zero_or, BitVec.or_zero, BitVec.zero_and, BitVec.and_zero,
      BitVec.or_allOnes, BitVec.allOnes_or, BitVec.and_allOnes, BitVec.allOnes_and]

private theorem reducedJoin_leaves (op : Bool) (a b : Reduced) :
    (reducedJoin op a b).leaves.Sublist (a.leaves ++ b.leaves) := by
  rcases a with (_ | _) | f <;> rcases b with (_ | _) | g <;> cases op <;>
    simp [reducedJoin, Reduced.leaves, Formula.leaves]

private def nonconstant (v : Table) : Bool := v != 0#12 && v != 4095#12

private def constants : Formula 12 → Reduced
  | .leaf v =>
    if v = 0#12 then .inl false else if v = 4095#12 then .inl true else .inr (.leaf v)
  | .join op l r => reducedJoin op (constants l) (constants r)

private theorem constants_value (f : Formula 12) : (constants f).value = f.eval := by
  induction f with
  | leaf v => by_cases h : v = 0#12 <;> by_cases h' : v = 4095#12 <;>
      simp [constants, Reduced.value, Formula.eval, h, h']
  | join op l r il ir => simp [constants, reducedJoin_value, il, ir, Formula.eval]

private theorem constants_leaves (f : Formula 12) :
    (constants f).leaves.Sublist (f.leaves.filter nonconstant) := by
  induction f with
  | leaf v => by_cases h : v = 0#12 <;> by_cases h' : v = 4095#12 <;>
      simp [constants, Reduced.leaves, Formula.leaves, nonconstant, h, h']
  | join op l r il ir =>
    rw [Formula.leaves, List.filter_append]
    exact (reducedJoin_leaves _ _ _).trans (il.append ir)

private theorem exclude_single_with_extra {f : Formula 12} {v : Table}
    (he : f.eval = 3187) (hp : f.leaves.Perm (liveInputs ++ [v]))
    (hbase : v ∈ bases) : False := by
  rcases List.mem_append.mp hbase with hv | hc
  · let outside := liveInputs.erase v
    have allocated : ([v] ++ outside).Perm liveInputs := (List.perm_cons_erase hv).symm
    have leaves : f.leaves.Perm (v :: v :: outside) :=
      (hp.trans (List.perm_append_singleton v _)).trans ((List.perm_cons_erase hv).cons v)
    exact no_once_shared (inner := .leaf v) (outer := f) allocated (.refl _) leaves he
  · have hnon : liveInputs.filter nonconstant = liveInputs := by decide
    have hn : nonconstant v = false := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> simp [nonconstant]
    have perm := hp.filter nonconstant
    rw [List.filter_append, hnon] at perm
    simp only [List.filter_cons, hn, Bool.false_eq_true, reduceIte, List.filter_nil, List.append_nil] at perm
    cases h : constants f with
    | inl b =>
      have hval := constants_value f
      rw [h, he] at hval
      cases b <;> contradiction
    | inr g =>
      have hval := constants_value f
      rw [h, he] at hval
      have hs := constants_leaves f
      rw [h] at hs
      change g.leaves.Sublist _ at hs
      have hsup : ∀ t ∈ g.leaves, t ∈ bases := fun t ht =>
        List.mem_append_left _ (perm.mem_iff.mp (hs.subset ht))
      have hall : liveInputs ⊆ g.leaves :=
        fun _ ht => input_required (f := g) hval hsup ht
      have hsub : g.leaves.Subperm liveInputs := List.subperm_iff.mpr ⟨_, perm, hs⟩
      have hrev := List.subperm_of_subset (by decide : liveInputs.Nodup) hall
      exact no_read_once g (hsub.antisymm hrev) hval

theorem no_seven_rule_trace {rs : List Rule} (trace : CorrectTrace rs) (limit : rs.length ≤ 7) :
    (3187 : Table) ∉ available rs := by
  intro root
  let uses := pending rs [3187]
  let spent := totalCost rs [3187]
  have budget := totalCost_eq rs [3187]
  change uses.length + spent = 1 + rs.length at budget
  have hsubset : liveInputs ⊆ uses := mandatory_inputs trace root
  have hsup : ∀ t ∈ uses, t ∈ bases := pending_available trace (uses := [3187]) (by
    intro v hv
    simpa only [List.mem_singleton.mp hv] using root)
  have hnd : liveInputs.Nodup := by decide
  obtain ⟨sub, hpSub, hsub⟩ := List.subperm_of_subset hnd hsubset
  obtain ⟨extra, hpExtra⟩ := hsub.exists_perm_append
  have parts := hpExtra.trans (hpSub.append_right extra)
  have len := parts.length_eq
  have lbase : liveInputs.length = 7 := rfl
  rw [List.length_append, lbase] at len
  have hshape : Shape 3187 uses spent :=
    shape_of_cost trace [3187] (.leaf 3187) (.refl _) (by
      intro v hv
      simpa only [List.mem_singleton.mp hv] using root)
      (at_most_one_nonordinary_read trace root limit).1
  cases hshape with
  | single f he hp =>
    cases extra with
    | nil => exact no_read_once f (hp.trans (by simpa using parts)) he
    | cons v more =>
      have empty : more = [] := by
        apply List.length_eq_zero_iff.mp
        simp only [List.length_cons] at len
        omega
      subst more
      have vbase := hsup v (parts.mem_iff.mpr (List.mem_append_right _ (by simp)))
      exact exclude_single_with_extra he (hp.trans parts) vbase
  | paired outer inner outside he ho hl hcharged =>
    have empty : extra = [] := by
      apply List.length_eq_zero_iff.mp
      omega
    subst extra
    exact no_once_shared (hl.trans (by simpa using parts)) (.refl _) ho he

end Promise20754
