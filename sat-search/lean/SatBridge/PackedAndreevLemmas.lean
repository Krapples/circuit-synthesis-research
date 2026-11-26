import SatBridge.UnitClauses
import Mathlib

/-! Local token layout, width, and reader inequalities for packed Andreev projections. -/
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
    simp [digitPairs] at ih ⊢; omega

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
  have h (bits : List Bool) (sign : Bool) :
      (encodeLiteral (identifier bits, sign)).length = 2 * bits.length + 6 := by
    have hd := digitPairs_length bits
    simp [encodeLiteral, digitPairs, List.flatMap_append, List.append_assoc] at hd ⊢
    omega
  simp [chunkClauses, encodeCNF, encodeClause, h]
  omega

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

/-- Symbolic paired grammar for the literals carrying a chunk's low identifier digits. -/
def programmedLiteral (low : List ℕ) (tag : List Bool) (sign : Bool) :
    List (Bool ⊕ ℕ) :=
  [Sum.inl true, Sum.inl sign] ++
    (low.flatMap fun i => [Sum.inl true, Sum.inr i]) ++
    (digitPairs tag ++ [true, true, false, true]).map Sum.inl

def chunkPattern (z tag : List Bool) (low : List ℕ) : List (Bool ⊕ ℕ) :=
  (encodeLiteral (identifier z, false)).map Sum.inl ++ programmedLiteral low tag true ++
    [Sum.inl false, Sum.inl false] ++
    (encodeLiteral (identifier z, true)).map Sum.inl ++ programmedLiteral low tag false ++
    [Sum.inl false, Sum.inl false]

private theorem programmedLiteral_eval (low : List ℕ) (tag : List Bool) (sign : Bool)
    (x : Assignment) :
    (programmedLiteral low tag sign).map (Sum.elim id x) =
      encodeLiteral (identifier (low.map x ++ tag), sign) := by
  simp [programmedLiteral, encodeLiteral, digitPairs, List.map_flatMap,
    List.flatMap_map, List.flatMap_append, List.append_assoc]

theorem chunkPattern_eval (z tag : List Bool) (low : List ℕ) (x : Assignment) :
    (chunkPattern z tag low).map (Sum.elim id x) =
      encodeCNF (chunkClauses (identifier z) (identifier (low.map x ++ tag))) := by
  simp [chunkPattern, programmedLiteral_eval, chunkClauses, encodeCNF,
    encodeClause, List.append_assoc]

/-- Erase fixed bits and retain the source coordinate attached to each variable bit. -/
def coord (b : Bool ⊕ ℕ) : Option ℕ := Sum.elim (fun _ => none) some b

@[simp] theorem coord_inl (b : Bool) : coord (.inl b) = none := rfl

@[simp] theorem coord_inr (i : ℕ) : coord (.inr i) = some i := rfl

theorem chunkPattern_sources (z tag : List Bool) (low : List ℕ) :
    (chunkPattern z tag low).filterMap coord = low ++ low := by
  have fixed (w : List Bool) :
      ((w.map Sum.inl : List (Bool ⊕ ℕ)).filterMap coord) = [] := by
    induction w <;> simp_all [List.filterMap_map, Function.comp_def]
  have pairs : (low.flatMap fun i => [Sum.inl true, Sum.inr i]).filterMap coord = low := by
    induction low with
    | nil => rfl
    | cons i lo ih =>
      rw [List.flatMap_cons, List.filterMap_append, ih]
      rfl
  have h (sign : Bool) : (programmedLiteral low tag sign).filterMap coord = low := by
    simp only [programmedLiteral, List.filterMap_append, pairs, fixed]
    simp
  have endClause : ([Sum.inl false, Sum.inl false] : List (Bool ⊕ ℕ)).filterMap coord = [] := rfl
  simp only [chunkPattern, List.filterMap_append, h, fixed]
  simp [endClause]

/-- A replacement of a fixed-width auxiliary identifier or tag moves no source positions. -/
theorem chunkPattern_positions (z z' tag tag' : List Bool) (low : List ℕ)
    (hz : z.length = z'.length) (ht : tag.length = tag'.length) :
    (chunkPattern z tag low).map coord = (chunkPattern z' tag' low).map coord := by
  have blank (w : List Bool) :
      ((w.map Sum.inl : List (Bool ⊕ ℕ)).map coord) = List.replicate w.length none := by
    induction w <;> simp_all [Function.comp_def, List.replicate_succ]
  have lit (z : List Bool) (s : Bool) :
      (encodeLiteral (identifier z, s)).length = 2 * z.length + 6 := by
    have h := digitPairs_length z
    simp [encodeLiteral, digitPairs, List.flatMap_append, List.append_assoc] at h ⊢
    omega
  have prog (s : Bool) :
      (programmedLiteral low tag s).map coord = (programmedLiteral low tag' s).map coord := by
    simp [programmedLiteral, blank, digitPairs_length, ht, coord]
  simp [chunkPattern, blank, lit, hz, prog, coord]

/-- Equal-width retagging of an entire list of chunks preserves the coordinate mask. -/
theorem chunkPatterns_positions (zs zs' : List (List Bool)) (tag : List Bool)
    (lows : List (List ℕ)) (h : List.Forall₂ (fun a b : List Bool => a.length = b.length) zs zs') :
    ((zs.zipWith (fun z lo => chunkPattern z tag lo) lows).flatten).map coord =
      ((zs'.zipWith (fun z lo => chunkPattern z tag lo) lows).flatten).map coord := by
  induction h generalizing lows with
  | nil => rfl
  | cons h _ ih =>
    cases lows with
    | nil => rfl
    | cons lo lows =>
      simp only [List.zipWith_cons_cons, List.flatten_cons, List.map_append]
      rw [chunkPattern_positions _ _ _ _ _ h rfl, ih]

end SatBridge.PackedAndreev
