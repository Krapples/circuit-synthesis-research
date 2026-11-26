import SatBridge.UnitClauses
import Mathlib

/-!
Draft local lemmas for the permutable packed Andreev projection.
Intended location: sat-search/lean/SatBridge/PackedAndreevLemmas.lean.
This source has NOT been elaborated or checked in the pinned Lean environment.
It contains no declared axioms or `sorry`; it is not a formal verification claim.
The complete CNF gadget, permutation allocation, and circuit unfolding still need
integration. Tal's theorem is deliberately not declared as an axiom here.
-/
namespace SatBridge.PackedAndreev
open PEqualNP.Search
open SatBridge

def digitPairs (bits : List Bool) : List Bool :=
  bits.flatMap fun b => [true, b]

@[simp] theorem digitPairs_length (bits : List Bool) :
    (digitPairs bits).length = 2 * bits.length := by
  induction bits with
  | nil => rfl
  | cons b bs ih =>
    simp [digitPairs] at ih ⊢ <;> omega

/-- The actual grammar separates a programmable low-bit segment from its fixed
high tag. `identifier` supplies the final high one and canonicality. -/
theorem unit_layout (low tag : List Bool) (sign : Bool) :
    encodeClause [(identifier (low ++ tag), sign)] =
      [true, sign] ++ digitPairs low ++ digitPairs tag ++
        [true, true, false, true, false, false] := by
  rw [encode_identifier_unit]
  simp [digitPairs, List.flatMap_append, List.append_assoc]

/-- Equal-length low segments and equal-length tags preserve the exact word
length; signs do not change length either. -/
theorem equal_unit_width (a b u v : List Bool) (s t : Bool)
    (hlow : a.length = b.length) (htag : u.length = v.length) :
    (encodeClause [(identifier (a ++ u), s)]).length =
      (encodeClause [(identifier (b ++ v), t)]).length := by
  rw [encode_identifier_unit_length, encode_identifier_unit_length]
  simp only [List.length_append, hlow, htag]

/-- Two clauses force the chunk's auxiliary bit to equal its dictionary bit. -/
def chunkClauses (z u : ℕ) : CNF :=
  [[(z, false), (u, true)], [(z, true), (u, false)]]

theorem chunkClauses_eval (σ : Assignment) (z u : ℕ) :
    CNF.eval σ (chunkClauses z u) = true ↔ σ z = σ u := by
  cases hz : σ z <;> cases hu : σ u <;>
    simp [chunkClauses, CNF.eval, Clause.eval, Literal.eval, hz, hu]

/-- Fixed-width chunk blocks have length independent of the encoded patterns.
The supplied lists omit the canonical final high one. -/
theorem chunk_block_length (z u : List Bool) :
    (encodeCNF (chunkClauses (identifier z) (identifier u))).length =
      4 * z.length + 4 * u.length + 28 := by
  simp [chunkClauses, encodeCNF, encodeClause, encodeLiteral,
    List.flatMap_append, ← digitPairs, List.append_assoc] <;> omega

/-- Ordered disjoint numerical intervals. This is the telescoping invariant
for the largest and smallest row counts in sorted round-robin allocation. -/
def gapChain (lo : ℕ) : ℕ → List (ℕ × ℕ) → Prop
  | hi, [] => lo ≤ hi
  | hi, (a,b) :: xs => a ≤ hi ∧ b ≤ a ∧ gapChain lo b xs

theorem gapChain_sum (lo hi : ℕ) (xs : List (ℕ × ℕ))
    (h : gapChain lo hi xs) :
    (xs.map (fun ab => ab.1 - ab.2)).sum + lo ≤ hi := by
  induction xs generalizing hi with
  | nil => simpa [gapChain] using h
  | cons ab xs ih =>
    rcases ab with ⟨a,b⟩
    simp only [gapChain] at h
    obtain ⟨ha, hb, ht⟩ := h
    have hh := ih b ht
    simp only [List.map_cons, List.sum_cons]
    omega

/-- A list of operand occurrences, not a set of distinct consumer gates. -/
theorem sum_le_degree_mul (xs : List ℕ) (B : ℕ)
    (h : ∀ x ∈ xs, x ≤ B) : xs.sum ≤ xs.length * B := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha := h a (by simp)
    have ht : ∀ x ∈ xs, x ≤ B := fun x hx => h x (by simp [hx])
    have hh := ih ht
    simp only [List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- One heavy reader exists when total path mass exceeds degree times threshold. -/
theorem reader_above_of_mass (xs : List ℕ) (T : ℕ)
    (h : xs.length * T < xs.sum) : ∃ x ∈ xs, T < x := by
  by_contra! hn
  exact (Nat.not_lt_of_ge (sum_le_degree_mul xs T hn)) h

/-- Degree-capped form of the same local transfer. -/
theorem reader_above_of_degree_cap (xs : List ℕ) (D T : ℕ)
    (hd : xs.length ≤ D) (h : D * T < xs.sum) :
    ∃ x ∈ xs, T < x := by
  apply reader_above_of_mass xs T
  exact lt_of_le_of_lt (Nat.mul_le_mul_right T hd) h

end SatBridge.PackedAndreev
