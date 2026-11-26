import Mathlib

/-! A wire-cost construction for the conjunction-list normal form. -/

namespace ConjunctionCompiler

abbrev Signal (V : Type*) := (V → Bool) → Bool

/-- The index of a gate's output is the environment length before it is appended. -/
structure Gate where
  isOr : Bool
  left : ℕ
  right : ℕ

def Gate.eval {V : Type*} (g : Gate) (wires : List (Signal V)) : Signal V := fun x =>
  let a := (wires[g.left]?.getD (fun _ => false)) x
  let b := (wires[g.right]?.getD (fun _ => false)) x
  if g.isOr then a || b else a && b

def eval {V : Type*} (start : List (Signal V)) (gates : List Gate) : List (Signal V) :=
  gates.foldl (fun wires g => wires ++ [g.eval wires]) start

def ref {V : Type*} (wires : List (Signal V)) (i : ℕ) : Signal V :=
  wires[i]?.getD (fun _ => false)

def conjunction {V : Type*} (wires : List (Signal V)) (indices : List ℕ) : Signal V :=
  fun x => indices.all (fun i => ref wires i x)

def orCount (gates : List Gate) : ℕ := gates.countP Gate.isOr

theorem orCount_append (a b : List Gate) : orCount (a ++ b) = orCount a + orCount b := by
  simp [orCount, List.countP_append]

theorem eval_append {V : Type*} (start : List (Signal V)) (a b : List Gate) :
    eval start (a ++ b) = eval (eval start a) b := by
  simp [eval, List.foldl_append]

theorem eval_prefix {V : Type*} (start : List (Signal V)) (gates : List Gate) :
    ∃ tail, eval start gates = start ++ tail := by
  induction gates generalizing start with
  | nil => exact ⟨[], by simp [eval]⟩
  | cons g rest ih =>
    obtain ⟨tail, eq⟩ := ih (start ++ [g.eval start])
    exact ⟨g.eval start :: tail, by simpa [eval, List.append_assoc] using eq⟩

theorem ref_preserved {V : Type*} (start : List (Signal V)) (gates : List Gate) {i : ℕ}
    (inside : i < start.length) : ref (eval start gates) i = ref start i := by
  obtain ⟨tail, eq⟩ := eval_prefix start gates
  simp [eq, ref, List.getElem?_append_left inside]

theorem conjunction_preserved {V : Type*} (start : List (Signal V)) (indices : List ℕ)
    (inside : ∀ i ∈ indices, i < start.length) (gates : List Gate) :
    conjunction (eval start gates) indices = conjunction start indices := by
  induction indices with
  | nil => rfl
  | cons i rest ih =>
    have top := ref_preserved start gates (inside i (by simp))
    have tail := ih (fun j hj => inside j (by simp [hj]))
    funext x
    change (ref (eval start gates) i x && conjunction (eval start gates) rest x) =
      (ref start i x && conjunction start rest x)
    rw [top, tail]

theorem ref_last {V : Type*} (wires : List (Signal V)) (s : Signal V) :
    ref (wires ++ [s]) wires.length = s := by
  simp [ref]

theorem emit_conjunction {V : Type*} (start : List (Signal V)) (indices : List ℕ)
    (inside : ∀ i ∈ indices, i < start.length) (one : ℕ) (oneValid : one < start.length)
    (oneTrue : ref start one = fun _ => true) :
    ∃ gates out, orCount gates = 0 ∧ out < (eval start gates).length ∧
      ref (eval start gates) out = conjunction start indices := by
  induction indices with
  | nil => exact ⟨[], one, rfl, oneValid, oneTrue⟩
  | cons j rest ih =>
    obtain ⟨gates, out, cost, outValid, agree⟩ := ih (fun i hi => inside i (by simp [hi]))
    let prior := eval start gates
    let g : Gate := ⟨false, j, out⟩
    have old := ref_preserved start gates (inside j (by simp))
    refine ⟨gates ++ [g], prior.length, ?_, ?_, ?_⟩
    · rw [orCount_append, cost]
      rfl
    · simp [eval, prior]
    · rw [eval_append]
      change ref (prior ++ [g.eval prior]) prior.length = _
      rw [ref_last]
      funext x
      change (ref prior j x && ref prior out x) = (ref start j x && conjunction start rest x)
      rw [show ref prior j = ref start j from old, show ref prior out = conjunction start rest from agree]

section Updates

variable {V I : Type*}

def updateSignals (signals : I → Signal V) (a b : I) (use : I → Bool) : I → Signal V :=
  fun t x => if use t then signals t x && (signals a x || signals b x) else signals t x

def Factors (wires : List (Signal V)) (signals : I → Signal V) (factors : I → List ℕ) : Prop :=
  ∀ t, (∀ i ∈ factors t, i < wires.length) ∧ conjunction wires (factors t) = signals t

theorem emit_update (start : List (Signal V)) (signals : I → Signal V) (factors : I → List ℕ)
    (rep : Factors start signals factors) (one : ℕ) (oneValid : one < start.length)
    (oneTrue : ref start one = fun _ => true) (a b : I) (use : I → Bool) :
    ∃ gates next, orCount gates = 1 ∧ Factors (eval start gates) (updateSignals signals a b use) next := by
  obtain ⟨ag, an, acost, aval, afun⟩ := emit_conjunction start (factors a) (rep a).1 one oneValid oneTrue
  let mid := eval start ag
  have midBound : start.length ≤ mid.length := by
    obtain ⟨tail, eq⟩ := eval_prefix start ag
    change mid = start ++ tail at eq
    simp [eq]
  have midOne : ref mid one = fun _ => true := (ref_preserved start ag oneValid).trans oneTrue
  obtain ⟨bg, bn, bcost, bval, bfun⟩ := emit_conjunction mid (factors b)
    (fun i hi => ((rep b).1 i hi).trans_le midBound) one (oneValid.trans_le midBound) midOne
  let prior := eval mid bg
  let gate : Gate := ⟨true, an, bn⟩
  let k := prior.length
  let all := ag ++ bg ++ [gate]
  have wires : eval start all = prior ++ [gate.eval prior] := by
    simp only [all, eval_append]
    rfl
  have fullBound : start.length ≤ (eval start all).length := by
    obtain ⟨tail, eq⟩ := eval_prefix start all
    simp [eq]
  have aSignal : ref prior an = signals a := (ref_preserved mid bg aval).trans (afun.trans (rep a).2)
  have bSignal : ref prior bn = signals b :=
    bfun.trans ((conjunction_preserved start (factors b) (rep b).1 ag).trans (rep b).2)
  have newest : ref (eval start all) k = fun x => signals a x || signals b x := by
    rw [wires, show k = prior.length from rfl, ref_last]
    funext x
    change (ref prior an x || ref prior bn x) = _
    rw [aSignal, bSignal]
  refine ⟨all, (fun t => if use t then factors t ++ [k] else factors t), ?_, fun t => ?_⟩
  · simp only [all, orCount_append, acost, bcost]
    rfl
  · have baseEq := (conjunction_preserved start (factors t) (rep t).1 all).trans (rep t).2
    cases useT : use t with
    | false =>
      have unchanged : updateSignals signals a b use t = signals t := by
        funext x
        simp [updateSignals, useT]
      exact ⟨fun i hi => ((rep t).1 i (by simpa [useT] using hi)).trans_le fullBound,
        by simpa [useT, unchanged] using baseEq⟩
    | true =>
      simp only [useT, ite_true]
      constructor
      · intro i hi
        rcases List.mem_append.mp hi with old | new
        · exact ((rep t).1 i old).trans_le fullBound
        · obtain rfl := List.mem_singleton.mp new
          simp [wires, k]
      · funext x
        simp only [updateSignals, useT, ite_true]
        change ((factors t ++ [k]).all (fun i => ref (eval start all) i x)) = _
        rw [List.all_append]
        change (conjunction (eval start all) (factors t) x && (ref (eval start all) k x && true)) = _
        simp [baseEq, newest]

structure Rule (I : Type*) where
  left : I
  right : I
  use : I → Bool

def applyRule (signals : I → Signal V) (rule : Rule I) : I → Signal V :=
  updateSignals signals rule.left rule.right rule.use

theorem emit_updates (R : List (Rule I)) (start : List (Signal V)) (signals : I → Signal V) (factors : I → List ℕ)
    (rep : Factors start signals factors) (one : ℕ) (oneValid : one < start.length)
    (oneTrue : ref start one = fun _ => true) :
    ∃ gates next, orCount gates = R.length ∧ Factors (eval start gates) (R.foldl applyRule signals) next := by
  induction R generalizing start signals factors with
  | nil => exact ⟨[], factors, rfl, rep⟩
  | cons r rest ih =>
    obtain ⟨first, next, cost, fact⟩ := emit_update start signals factors rep one oneValid oneTrue r.left r.right r.use
    obtain ⟨tail, eq⟩ := eval_prefix start first
    have bound : one < (eval start first).length := by simpa [eq] using oneValid.trans_le (Nat.le_add_right start.length tail.length)
    have trueAgain := (ref_preserved start first oneValid).trans oneTrue
    obtain ⟨suffix, final, many, law⟩ := ih (eval start first) (applyRule signals r) next fact bound trueAgain
    exact ⟨first ++ suffix, final, by rw [orCount_append, cost, many]; simp [Nat.add_comm],
      by simpa only [List.foldl_cons, eval_append] using law⟩

theorem emit_output (R : List (Rule I)) (start : List (Signal V)) (signals : I → Signal V) (factors : I → List ℕ)
    (rep : Factors start signals factors) (one : ℕ) (oneValid : one < start.length)
    (oneTrue : ref start one = fun _ => true) (t : I) :
    ∃ gates out, orCount gates = R.length ∧ out < (eval start gates).length ∧
      ref (eval start gates) out = (R.foldl applyRule signals) t := by
  obtain ⟨core, next, cost, hnext⟩ := emit_updates R start signals factors rep one oneValid oneTrue
  obtain ⟨tail, eq⟩ := eval_prefix start core
  have bound : one < (eval start core).length := by simpa [eq] using oneValid.trans_le (Nat.le_add_right start.length tail.length)
  obtain ⟨join, out, noCost, valid, agree⟩ := emit_conjunction (eval start core) (next t) (hnext t).1 one bound
    ((ref_preserved start core oneValid).trans oneTrue)
  exact ⟨core ++ join, out, by rw [orCount_append, cost, noCost]; simp,
    by simpa only [eval_append] using valid, by rw [eval_append, agree, (hnext t).2]⟩

end Updates

section Covers

variable {V A : Type*}

def unionStep (available : Set (Set A)) (r : Set A × Set A) : Set (Set A) :=
  {S | S ∈ available ∨ (r.1 ∈ available ∧ r.2 ∈ available ∧ S ⊆ r.1 ∪ r.2)}

noncomputable def failSignals (available : (V → Bool) → Set (Set A)) : Set A → Signal V := by
  classical exact fun S x => !decide (S ∈ available x)

noncomputable def unionRule (r : Set A × Set A) : Rule (Set A) := by
  classical exact ⟨r.1, r.2, fun S => decide (S ⊆ r.1 ∪ r.2)⟩

theorem fold_fail (R : List (Set A × Set A)) (avail : (V → Bool) → Set (Set A)) :
    (R.map unionRule).foldl applyRule (failSignals avail) =
      failSignals (fun x => R.foldl unionStep (avail x)) := by
  classical
  induction R generalizing avail with
  | nil => rfl
  | cons r R ih =>
    have commutes : applyRule (failSignals avail) (unionRule r) = failSignals (fun x => unionStep (avail x) r) := by
      funext S x
      by_cases use : S ⊆ r.1 ∪ r.2 <;> by_cases t : S ∈ avail x <;>
        by_cases a : r.1 ∈ avail x <;> by_cases b : r.2 ∈ avail x <;>
        simp [applyRule, updateSignals, failSignals, unionRule, unionStep, use, t, a, b]
    change (R.map unionRule).foldl applyRule (applyRule (failSignals avail) (unionRule r)) = _
    rw [commutes, ih]
    rfl

def covered (ends : A → V × V) (x : V → Bool) (e : A) : Prop :=
  x (ends e).1 = false ∨ x (ends e).2 = false

def stars (ends : A → V × V) (x : V → Bool) : Set (Set A) :=
  {S | S = ∅ ∨ ∃ v, x v = false ∧ ∀ e ∈ S, (ends e).1 = v ∨ (ends e).2 = v}

theorem union_sound (ends : A → V × V) (x : V → Bool) (R : List (Set A × Set A))
    (avail : Set (Set A)) (initial : ∀ S ∈ avail, ∀ e ∈ S, covered ends x e) :
    ∀ S ∈ R.foldl unionStep avail, ∀ e ∈ S, covered ends x e := by
  induction R generalizing avail with
  | nil => exact initial
  | cons r rest ih =>
    apply ih (unionStep avail r)
    intro S h e he
    rcases h with old | ⟨a, b, incl⟩
    · exact initial S old e he
    · rcases incl he with left | right
      · exact initial r.1 a e left
      · exact initial r.2 b e right

noncomputable def edgeSignal (ends : A → V × V) (E : Set A) : Signal V := by
  classical exact fun x => decide (∃ e ∈ E, x (ends e).1 = true ∧ x (ends e).2 = true)

theorem compile_cover_union (ends : A → V × V) (R : List (Set A × Set A)) (E : Set A)
    (common : ∀ x, (∀ e ∈ E, covered ends x e) → E ∈ R.foldl unionStep (stars ends x))
    (start : List (Signal V)) (factors : Set A → List ℕ)
    (initial : Factors start (failSignals (stars ends)) factors)
    (one : ℕ) (oneValid : one < start.length) (oneTrue : ref start one = fun _ => true) :
    ∃ gates out, orCount gates = R.length ∧ out < (eval start gates).length ∧
      ref (eval start gates) out = edgeSignal ends E := by
  classical
  obtain ⟨gates, out, cost, valid, agree⟩ := emit_output (R.map unionRule) start _ factors initial one oneValid oneTrue E
  refine ⟨gates, out, by simpa using cost, valid, ?_⟩
  rw [agree, fold_fail]
  funext x
  have initialSound : ∀ S ∈ stars ends x, ∀ e ∈ S, covered ends x e := by
    intro S available e he
    rcases available with empty | ⟨v, off, all⟩
    · exact (empty ▸ he).elim
    · rcases all e he with left | right
      · exact Or.inl (left ▸ off)
      · exact Or.inr (right ▸ off)
  have coverEquiv : E ∈ R.foldl unionStep (stars ends x) ↔ ∀ e ∈ E, covered ends x e :=
    ⟨fun h => union_sound ends x R (stars ends x) initialSound E h, common x⟩
  by_cases live : ∃ e ∈ E, x (ends e).1 = true ∧ x (ends e).2 = true
  · obtain ⟨e, he, hl, hr⟩ := live
    have no : E ∉ R.foldl unionStep (stars ends x) := fun h => by
      rcases coverEquiv.mp h e he with left | right
      · simp [hl] at left
      · simp [hr] at right
    simp [failSignals, edgeSignal, no, show ∃ e ∈ E, x (ends e).1 = true ∧ x (ends e).2 = true from ⟨e, he, hl, hr⟩]
  · have yes : E ∈ R.foldl unionStep (stars ends x) := coverEquiv.mpr (fun e he => by
      cases l : x (ends e).1 <;> cases r : x (ends e).2 <;>
        simp_all [covered])
    simp [failSignals, edgeSignal, yes, live]

noncomputable def starFactors [Fintype V] (ends : A → V × V) (vertex : V → ℕ) (zeroIndex : ℕ)
    (S : Set A) : List ℕ := by
  classical exact if S = ∅ then [zeroIndex] else
    ((Finset.univ.filter fun v => ∀ e ∈ S, (ends e).1 = v ∨ (ends e).2 = v).toList.map vertex)

theorem initial_star_factors [Fintype V] (ends : A → V × V) (start : List (Signal V))
    (vertex : V → ℕ) (vertexValid : ∀ v, vertex v < start.length)
    (vertexValue : ∀ v, ref start (vertex v) = fun x => x v)
    (zeroIndex : ℕ) (zeroValid : zeroIndex < start.length) (zeroValue : ref start zeroIndex = fun _ => false) :
    Factors start (failSignals (stars ends)) (starFactors ends vertex zeroIndex) := by
  classical
  intro S
  by_cases empty : S = ∅
  · constructor
    · intro i hi
      have member : i ∈ [zeroIndex] := by simpa [starFactors, empty] using hi
      obtain rfl := List.mem_singleton.mp member
      exact zeroValid
    · funext x
      simp [starFactors, empty, conjunction, zeroValue, failSignals, stars]
  · constructor
    · intro i hi
      simp only [starFactors, ite_eq_right empty, List.mem_map] at hi
      obtain ⟨v, _, rfl⟩ := hi
      exact vertexValid v
    · funext x
      have iffTrue : conjunction start (starFactors ends vertex zeroIndex S) x = true ↔
          failSignals (stars ends) S x = true := by
        have failTrue : failSignals (stars ends) S x = true ↔ S ∉ stars ends x := by simp [failSignals]
        rw [failTrue]
        simp only [conjunction, List.all_eq_true, starFactors, ite_eq_right empty, List.mem_map, Finset.mem_toList,
          Finset.mem_filter, Finset.mem_univ, true_and]
        change (∀ i, (∃ v, (∀ e ∈ S, (ends e).1 = v ∨ (ends e).2 = v) ∧ vertex v = i) → ref start i x = true) ↔
          ¬ (S = ∅ ∨ ∃ v, x v = false ∧ ∀ e ∈ S, (ends e).1 = v ∨ (ends e).2 = v)
        constructor
        · intro yes avail
          rcases avail with impossible | ⟨v, off, centered⟩
          · exact empty impossible
          · have on := yes (vertex v) ⟨v, centered, rfl⟩
            rw [vertexValue] at on
            change x v = true at on
            rw [off] at on
            exact Bool.noConfusion on
        · intro fail i hi
          obtain ⟨v, centered, rfl⟩ := hi
          rw [vertexValue]
          cases value : x v
          · exact (fail (Or.inr ⟨v, value, centered⟩)).elim
          · exact value
      cases h₁ : conjunction start (starFactors ends vertex zeroIndex S) x <;>
        cases h₂ : failSignals (stars ends) S x <;> simp_all

theorem compile_finite_cover_union [Fintype V] (ends : A → V × V) (R : List (Set A × Set A)) (E : Set A)
    (common : ∀ x, (∀ e ∈ E, covered ends x e) → E ∈ R.foldl unionStep (stars ends x))
    (start : List (Signal V)) (vertex : V → ℕ) (vertexValid : ∀ v, vertex v < start.length)
    (vertexValue : ∀ v, ref start (vertex v) = fun x => x v)
    (zeroIndex : ℕ) (zeroValid : zeroIndex < start.length) (zeroValue : ref start zeroIndex = fun _ => false)
    (one : ℕ) (oneValid : one < start.length) (oneTrue : ref start one = fun _ => true) :
    ∃ gates out, orCount gates = R.length ∧ out < (eval start gates).length ∧
      ref (eval start gates) out = edgeSignal ends E :=
  compile_cover_union ends R E common start (starFactors ends vertex zeroIndex)
    (initial_star_factors ends start vertex vertexValid vertexValue zeroIndex zeroValid zeroValue) one oneValid oneTrue

end Covers

end ConjunctionCompiler
