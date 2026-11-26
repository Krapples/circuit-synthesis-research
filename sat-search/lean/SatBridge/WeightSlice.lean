import SatBridge.UnitClauses
import PEqualNP.Library.SearchHelpers.SatVerifier

/-! A signed projection of the paired SAT grammar into one Hamming slice. -/

namespace SatBridge
open PEqualNP.Search PEqualNP.Library.SearchHelpers.SatV

private def pairBoundary : WS → Prop
  | .a | .b | .c | .d | .dead => True
  | _ => False

private theorem pair_step (q : WS) (h : pairBoundary q) (a b : Bool) :
    pairBoundary (wfD (wfD q a) b) := by
  cases q <;> cases a <;> cases b <;> simp_all [pairBoundary, wfD]

private theorem fold_boundary : ∀ (xs : List Bool) (q : WS),
    pairBoundary q → xs.length % 2 = 0 → pairBoundary (xs.foldl wfD q)
  | [], _, h, _ => h
  | [_], _, _, h => by simp at h
  | a :: b :: xs, q, h, he => by
    simp only [List.foldl_cons]
    apply fold_boundary xs _ (pair_step q h a b)
    simp only [List.length_cons] at he
    omega

private theorem end_token (q : WS) (h : pairBoundary q) :
    wfD (wfD q false) false = .a ∨ wfD (wfD q false) false = .dead := by
  cases q <;> simp_all [pairBoundary, wfD]

/-- A well-formed suffix consisting of a tautological clause can be stripped after
an aligned end-of-clause token, even if the prefix was not assumed well-formed. -/
theorem sat_append_tautology_aligned (xs : List Bool) (h : xs.length % 2 = 0)
    (cl : Clause) (hcl : ∀ σ : Assignment, Clause.eval σ cl = true) :
    (xs ++ [false, false] ++ encodeClause cl) ∈ SAT ↔ (xs ++ [false, false]) ∈ SAT := by
  let pre := xs ++ [false, false]
  change (pre ++ encodeClause cl) ∈ SAT ↔ pre ∈ SAT
  constructor
  · rintro ⟨φ, hφ, ⟨σ, hσ⟩⟩
    have ha : (pre ++ encodeClause cl).foldl wfD .a = .a := hφ ▸ foldl_cnf φ
    have p : pre.foldl wfD .a = .a ∨ pre.foldl wfD .a = .dead := by
      simpa [pre, List.foldl_append] using end_token _ (fold_boundary xs WS.a trivial h)
    have hp : pre.foldl wfD .a = .a := by
      rcases p with p | p
      · exact p
      · simp [List.foldl_append, p, foldl_dead] at ha
    obtain ⟨ψ, hψ⟩ := (wfB_iff pre).mp (by simp [wfB, hp])
    have hh : encodeCNF (ψ ++ [cl]) = encodeCNF φ := by
      rw [hφ, ← hψ]
      simp [encodeCNF, List.flatMap_append]
    have hf := PEqualNP.Library.SearchHelpers.encodeCNF_injective hh
    rw [← hf] at hσ
    exact ⟨ψ, hψ, σ, by simpa [CNF.eval, hcl] using hσ⟩
  · rintro ⟨ψ, hψ, ⟨σ, hσ⟩⟩
    refine ⟨ψ ++ [cl], ?_, σ, ?_⟩
    · change (ψ ++ [cl]).flatMap encodeClause = pre ++ encodeClause cl
      simp [List.flatMap_append, ← hψ, encodeCNF]
    · simp [CNF.eval, hcl, CNF.eval] at hσ ⊢
      exact hσ

/-- Add the complements of all payload bits as digits of a literal in a tautology. -/
def weightSliceWord (xs : List Bool) : List Bool :=
  xs ++ [false, false, true, false, false, true, true, true, false, true, true, false] ++
    (xs.flatMap fun b => [true, !b]) ++ [true, true, false, true, false, false]

theorem weightSliceWord_sat (xs : List Bool) (h : xs.length % 2 = 0) :
    weightSliceWord xs ∈ SAT ↔ (xs ++ [false, false]) ∈ SAT := by
  let cl : Clause := [(0, false), (0, true), (identifier (xs.map (! ·)), false)]
  have hcl (σ : Assignment) : Clause.eval σ cl = true := by
    cases h0 : σ 0 <;> simp [cl, Clause.eval, Literal.eval, h0]
  have hw : weightSliceWord xs = xs ++ [false, false] ++ encodeClause cl := by
    simp [weightSliceWord, cl, encodeClause, encodeLiteral, List.flatMap_append, List.flatMap_map,
      List.append_assoc]
  exact hw ▸ sat_append_tautology_aligned xs h cl hcl

theorem weightSliceWord_guard (xs : List Bool) (h : xs.length % 2 = 0) (a b : Bool) :
    (xs ++ [a, b]) ∈ SAT ↔ a = false ∧ b = false ∧ weightSliceWord xs ∈ SAT := by
  constructor
  · intro hs
    have acc : (xs ++ [a, b]).foldl wfD .a = .a := by
      obtain ⟨φ, hφ, _⟩ := hs
      exact hφ ▸ foldl_cnf φ
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil] at acc
    have phase : a = false ∧ b = false := by
      generalize e : xs.foldl wfD .a = q at acc
      have hb : pairBoundary q := e ▸ fold_boundary xs WS.a trivial h
      cases q <;> cases a <;> cases b <;> simp_all [pairBoundary, wfD]
    rcases phase with ⟨rfl, rfl⟩
    exact ⟨rfl, rfl, (weightSliceWord_sat xs h).mpr hs⟩
  · rintro ⟨rfl, rfl, hs⟩
    exact (weightSliceWord_sat xs h).mp hs

theorem weightSliceWord_length (xs : List Bool) : (weightSliceWord xs).length = 3 * xs.length + 18 := by
  have h : (xs.flatMap fun b => [true, !b]).length = 2 * xs.length := by
    induction xs with
    | nil => rfl
    | cons b bs ih => simp [ih]; omega
  simp only [weightSliceWord, List.length_append, h, List.length_cons, List.length_nil]
  omega

theorem weightSliceWord_weight (xs : List Bool) : (weightSliceWord xs).count true = 2 * xs.length + 9 := by
  have h : xs.count true + (xs.flatMap fun b => [true, !b]).count true = 2 * xs.length := by
    induction xs with
    | nil => decide
    | cons b bs ih => cases b <;> simp at ih ⊢ <;> omega
  simp only [weightSliceWord, List.count_append]
  have h₁ : ([false, false, true, false, false, true, true, true, false, true, true, false] : List Bool).count true = 6 := by decide
  have h₂ : ([true, true, false, true, false, false] : List Bool).count true = 3 := by decide
  omega

end SatBridge
