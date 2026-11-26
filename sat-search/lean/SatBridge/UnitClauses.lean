import PEqualNP.Library.SearchHelpers.Encoding

namespace SatBridge

open PEqualNP.Search

/-- An identifier with the given low bits followed by a fixed high one. -/
def identifier : List Bool → ℕ
  | [] => 1
  | b :: bs => Nat.bit b (identifier bs)

private theorem identifier_pos (bits : List Bool) : 0 < identifier bits := by
  induction bits with
  | nil => decide
  | cons b bs ih => cases b <;> simp [identifier, Nat.bit, ih]

@[simp] theorem identifier_bits (bits : List Bool) : (identifier bits).bits = bits ++ [true] := by
  induction bits with
  | nil => simp [identifier]
  | cons b bs ih =>
    rw [identifier, Nat.bits_append_bit _ _ (fun h => (Nat.ne_of_gt (identifier_pos bs) h).elim), ih]
    rfl

theorem identifier_injective : Function.Injective identifier := by
  intro a b h
  simpa only [identifier_bits, List.append_cancel_right_eq] using congrArg Nat.bits h

theorem encode_identifier_unit (bits : List Bool) (sign : Bool) :
    encodeClause [(identifier bits, sign)] =
      [true, sign] ++ (bits.flatMap fun b => [true, b]) ++ [true, true, false, true, false, false] := by
  simp [encodeClause, encodeLiteral, List.flatMap_append, List.append_assoc]

theorem encode_identifier_unit_length (bits : List Bool) (sign : Bool) :
    (encodeClause [(identifier bits, sign)]).length = 2 * bits.length + 8 := by
  have hl : (bits.flatMap fun b => [true, b]).length = 2 * bits.length := by
    induction bits with
    | nil => rfl
    | cons b bs ih => simp [ih]; omega
  rw [encode_identifier_unit]
  simp [hl]

/-- Negative helper clauses, positive query clauses, and positive padding clauses. -/
def unitCNF (forbidden queries padding : List ℕ) : CNF :=
  (forbidden.map fun v => [(v, false)]) ++ ((queries ++ padding).map fun v => [(v, true)])

/-- The encoding of a unit CNF is satisfiable exactly when no positive identifier is forbidden. -/
theorem unitCNF_mem_sat (forbidden queries padding : List ℕ) :
    encodeCNF (unitCNF forbidden queries padding) ∈ SAT ↔
      ∀ v ∈ queries ++ padding, v ∉ forbidden := by
  classical
  have eval_unit (σ : Assignment) (v : ℕ) (b : Bool) :
      Clause.eval σ [(v, b)] = true ↔ σ v = b := by
    simp [Clause.eval, Literal.eval]
  constructor
  · rintro ⟨φ, hφ, σ, hσ⟩ v hv hf
    have he := PEqualNP.Library.SearchHelpers.encodeCNF_injective hφ
    subst φ
    simp only [CNF.eval, List.all_eq_true] at hσ
    have hp := (eval_unit σ v true).mp (hσ _ (by
      simp [unitCNF, List.mem_append.mp hv]))
    have hn := (eval_unit σ v false).mp (hσ _ (by simp [unitCNF, hf]))
    simp [hp] at hn
  · intro h
    refine ⟨_, rfl, fun v => decide (v ∉ forbidden), ?_⟩
    simp only [CNF.eval, List.all_eq_true, unitCNF, List.mem_append, List.mem_map]
    rintro c (⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩)
    · exact (eval_unit _ _ _).mpr (by simp [hv])
    · exact (eval_unit _ _ _).mpr (by simp [h v (List.mem_append.mpr hv)])

/-- For a complete list of table rows, helpers encode the zero set of a Boolean test. -/
theorem unitCNF_table_mem_sat {α : Type} (rows queries : List α) (g : α → Bool)
    (ident : α → ℕ) (padding : List ℕ)
    (hrows : ∀ x, x ∈ rows) (hinj : Function.Injective ident)
    (hpad : ∀ v ∈ padding, ∀ x, v ≠ ident x) :
    encodeCNF (unitCNF ((rows.filter fun x => !g x).map ident) (queries.map ident) padding) ∈ SAT ↔
      ∀ x ∈ queries, g x = true := by
  rw [unitCNF_mem_sat]
  have helper (v : ℕ) :
      v ∈ (rows.filter fun x => !g x).map ident ↔ ∃ x, g x = false ∧ ident x = v := by
    simp [List.mem_map, List.mem_filter, hrows]
  constructor
  · intro h x hx
    cases hg : g x
    · exact (h (ident x) (List.mem_append_left _ (List.mem_map_of_mem hx))
        ((helper _).mpr ⟨x, hg, rfl⟩)).elim
    · rfl
  · intro h v hv hf
    obtain ⟨x, hg, he⟩ := (helper _).mp hf
    rcases List.mem_append.mp hv with hv | hv
    · obtain ⟨y, hy, hyv⟩ := List.mem_map.mp hv
      have hxy := hinj (he.trans hyv.symm)
      subst y
      simp [h x hy] at hg
    · exact hpad v hv x he.symm

private theorem padding_zero_length :
    ∀ k : ℕ, (encodeCNF (unitCNF [] [] (List.replicate k 0))).length = 6 * k
  | 0 => rfl
  | k + 1 => by
    have ih := padding_zero_length k
    have h6 : (encodeClause [(0, true)]).length = 6 := by decide
    simp only [unitCNF, List.map_nil, List.nil_append, encodeCNF] at ih
    simp only [unitCNF, List.map_nil, List.nil_append, List.replicate_succ, List.map_cons,
      encodeCNF, List.flatMap_cons, List.length_append, h6, ih]
    omega

/-- Any even padding length of at least six is filled by positive unit clauses on 0, 1, and 2. -/
theorem exists_unit_padding (t : ℕ) (hte : t % 2 = 0) (ht : 6 ≤ t) :
    ∃ padding : List ℕ, (∀ v ∈ padding, v ≤ 2) ∧
      (encodeCNF (unitCNF [] [] padding)).length = t := by
  have h8 : (encodeClause [(1, true)]).length = 8 := by decide
  have h10 : (encodeClause [(2, true)]).length = 10 := by decide
  have hmod : t % 6 = 0 ∨ t % 6 = 2 ∨ t % 6 = 4 := by omega
  rcases hmod with hz | htwo | hfour
  · refine ⟨List.replicate (t / 6) 0, ?_, ?_⟩
    · intro v hv
      have := (List.eq_of_mem_replicate hv : v = 0)
      omega
    · rw [padding_zero_length]
      omega
  · refine ⟨1 :: List.replicate ((t - 8) / 6) 0, ?_, ?_⟩
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hm
      · decide
      · have := (List.eq_of_mem_replicate hm : v = 0)
        omega
    · have ih := padding_zero_length ((t - 8) / 6)
      simp only [unitCNF, List.map_nil, List.nil_append, encodeCNF] at ih
      simp only [unitCNF, List.map_nil, List.nil_append, List.map_cons, encodeCNF,
        List.flatMap_cons, List.length_append, h8, ih]
      omega
  · let k := (t - 10) / 6
    have hk : 10 + 6 * k = t := by dsimp [k]; omega
    refine ⟨2 :: List.replicate k 0, ?_, ?_⟩
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hm
      · decide
      · have := (List.eq_of_mem_replicate hm : v = 0)
        omega
    · have ih := padding_zero_length k
      simp only [unitCNF, List.map_nil, List.nil_append, List.map_cons, encodeCNF,
        List.flatMap_cons, List.length_append, h10]
      exact (congrArg (10 + ·) ih).trans hk

theorem padding_ne_identifier (bits : List Bool) (hr : 2 ≤ bits.length) {v : ℕ} (hv : v ≤ 2) :
    v ≠ identifier bits := by
  intro he
  have hbits : (identifier bits).bits.length = bits.length + 1 := by simp
  rw [← he] at hbits
  have hsmall : v.bits.length ≤ 2 := by
    rcases (show v = 0 ∨ v = 1 ∨ v = 2 by omega) with rfl | rfl | rfl <;> decide
  omega

end SatBridge
