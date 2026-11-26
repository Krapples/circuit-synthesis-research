/-
The six-bit SAT string identity (2026-11-26).

With `T(x, y) = 1 1 x 1 0 y` and the tail `1 1 0 1 0 0`,

  `T(x1,y1) ... T(xq,yq) 110100 ∈ SAT  ↔  ∀ j, xj = yj`.

`T(1,1)` is the literal `x1`, leaving the clause open; `T(0,0)` is the literal `x0` followed by the
end of the clause; the tail closes the last clause with `x0`. Every literal is positive, so the
all-true assignment satisfies the formula. A block with `x ≠ y` sends the external well-formedness
acceptor `wfD` to its dead state, so the string encodes no formula.
-/
import PEqualNP.Library.SearchHelpers.SatVerifier

namespace SatBridge

open PEqualNP.Search PEqualNP.Library.SearchHelpers.SatV

def blk (x y : Bool) : List Bool := [true, true, x, true, false, y]

def tail : List Bool := [true, true, false, true, false, false]

def word (ps : List (Bool × Bool)) : List Bool := ps.flatMap (fun p => blk p.1 p.2) ++ tail

theorem word_cons (p : Bool × Bool) (ps : List (Bool × Bool)) :
    word (p :: ps) = blk p.1 p.2 ++ word ps := by
  simp [word, List.append_assoc]

theorem blk_good (s : WS) (hs : s = .a ∨ s = .b) (x : Bool) :
    (blk x x).foldl wfD s = .a ∨ (blk x x).foldl wfD s = .b := by
  rcases hs with rfl | rfl <;> cases x <;> simp [blk, wfD]

theorem blk_bad (s : WS) (hs : s = .a ∨ s = .b) (x y : Bool) (h : x ≠ y) :
    (blk x y).foldl wfD s = .dead := by
  rcases hs with rfl | rfl <;> cases x <;> cases y <;> simp_all [blk, wfD]

theorem word_bad : ∀ (ps : List (Bool × Bool)) (s : WS), (s = .a ∨ s = .b) →
    (∃ p ∈ ps, p.1 ≠ p.2) → (word ps).foldl wfD s = .dead
  | [], _, _, ⟨p, hp, _⟩ => by simp at hp
  | p :: ps, s, hs, ⟨p', hp', hne⟩ => by
      rw [word_cons, List.foldl_append]
      by_cases hp : p.1 = p.2
      · have hrest : ∃ p ∈ ps, p.1 ≠ p.2 := by
          rcases List.mem_cons.1 hp' with rfl | h
          · exact absurd hp hne
          · exact ⟨p', h, hne⟩
        obtain ⟨a, b⟩ := p
        simp only at hp
        subst hp
        exact word_bad ps _ (blk_good s hs a) hrest
      · rw [blk_bad s hs _ _ hp, foldl_dead]

theorem word_not_sat (ps : List (Bool × Bool)) (h : ∃ p ∈ ps, p.1 ≠ p.2) : word ps ∉ SAT := by
  rintro ⟨φ, hφ, _⟩
  have hacc := foldl_cnf φ
  rw [hφ, word_bad ps .a (Or.inl rfl) h] at hacc
  exact absurd hacc (by decide)

/-- The formula: `true` adds the literal `x1` to the open clause, `false` adds `x0` and closes it. -/
def build : Clause → List Bool → CNF
  | acc, [] => [acc ++ [(0, true)]]
  | acc, true :: bs => build (acc ++ [(1, true)]) bs
  | acc, false :: bs => (acc ++ [(0, true)]) :: build [] bs

theorem enc_one : encodeLiteral (1, true) = blk true true := by
  simp [encodeLiteral, blk, Nat.one_bits]

theorem enc_zero : encodeLiteral (0, true) ++ [false, false] = blk false false := by
  simp [encodeLiteral, blk]

theorem build_enc : ∀ (bs : List Bool) (acc : Clause),
    acc.flatMap encodeLiteral ++ (bs.flatMap fun b => blk b b) ++ tail = encodeCNF (build acc bs)
  | [], acc => by
      simp [build, encodeCNF, encodeClause, encodeLiteral, tail]
  | true :: bs, acc => by
      show _ = encodeCNF (build (acc ++ [(1, true)]) bs)
      rw [← build_enc bs (acc ++ [(1, true)])]
      simp [enc_one, List.append_assoc]
  | false :: bs, acc => by
      have := build_enc bs []
      simp only [List.flatMap_nil, List.nil_append] at this
      simp only [build, encodeCNF, List.flatMap_cons, encodeClause, List.flatMap_append] at this ⊢
      rw [← this, ← enc_zero]
      simp [List.append_assoc]

theorem build_mem : ∀ (bs : List Bool) (acc : Clause), ∀ c ∈ build acc bs, ((0, true) : Literal) ∈ c
  | [], acc, c, hc => by simp [build] at hc; subst hc; simp
  | true :: bs, acc, c, hc => build_mem bs _ c hc
  | false :: bs, acc, c, hc => by
      simp only [build, List.mem_cons] at hc
      rcases hc with rfl | hc
      · simp
      · exact build_mem bs [] c hc

theorem word_sat (ps : List (Bool × Bool)) (h : ∀ p ∈ ps, p.1 = p.2) : word ps ∈ SAT := by
  have e : ps.flatMap (fun p => blk p.1 p.2) = (ps.map Prod.fst).flatMap fun b => blk b b := by
    rw [List.flatMap_map]
    exact List.flatMap_congr (fun p hp => by rw [h p hp])
  refine ⟨build [] (ps.map Prod.fst), ?_, fun _ => true, ?_⟩
  · rw [← build_enc]; simp [word, e]
  · simp only [CNF.eval, List.all_eq_true]
    intro c hc
    simp only [Clause.eval, List.any_eq_true]
    exact ⟨(0, true), build_mem _ _ c hc, by simp [Literal.eval]⟩

/-- **Six-bit string identity.** -/
theorem word_mem_sat (ps : List (Bool × Bool)) : word ps ∈ SAT ↔ ∀ p ∈ ps, p.1 = p.2 := by
  constructor
  · intro hs p hp
    by_contra hne
    exact word_not_sat ps ⟨p, hp, hne⟩ hs
  · exact word_sat ps

end SatBridge
