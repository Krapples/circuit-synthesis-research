import SatBridge.WeightSlice

/-! Exact paired-token projection of a topologically numbered XOR/mux program. -/
namespace SatBridge
open PEqualNP.Search

inductive LookupGate where
  | xor (a b : ℕ)
  | mux (s lo hi : ℕ)

namespace LookupGate

def value (x : Assignment) : LookupGate → Bool
  | .xor a b => x a ^^ x b
  | .mux s lo hi => if x s then x hi else x lo

def clauses (z : ℕ) : LookupGate → CNF
  | .xor a b =>
    [[(a,true),(b,true),(z,false)], [(a,true),(b,false),(z,true)],
     [(a,false),(b,true),(z,true)], [(a,false),(b,false),(z,false)]]
  | .mux s lo hi =>
    [[(s,true),(lo,false),(z,true)], [(s,true),(lo,true),(z,false)],
     [(s,false),(hi,false),(z,true)], [(s,false),(hi,true),(z,false)]]

def wellScoped (bound : ℕ) : LookupGate → Prop
  | .xor a b => a < bound ∧ b < bound
  | .mux s lo hi => s < bound ∧ lo < bound ∧ hi < bound

theorem value_congr {u v : Assignment} {n : ℕ} {g : LookupGate}
    (hg : g.wellScoped n) (h : ∀ i < n, u i = v i) : g.value u = g.value v := by
  cases g with
  | xor a b => simp [value, h a hg.1, h b hg.2]
  | mux s a b => simp [value, h s hg.1, h a hg.2.1, h b hg.2.2]

theorem clauses_eval (g : LookupGate) (z : ℕ) (x : Assignment) :
    CNF.eval x (g.clauses z) = true ↔ x z = g.value x := by
  cases g with
  | xor a b =>
    cases ha : x a <;> cases hb : x b <;> cases hz : x z <;>
      simp [clauses, value, CNF.eval, Clause.eval, Literal.eval, ha, hb, hz]
  | mux s a b =>
    cases hs : x s <;> cases ha : x a <;> cases hb : x b <;> cases hz : x z <;>
      simp [clauses, value, CNF.eval, Clause.eval, Literal.eval, hs, ha, hb, hz]

end LookupGate

/-- Programs are stored newest first. The newest output follows all earlier wire IDs. -/
def lookupCNF (d : ℕ) : List LookupGate → CNF
  | [] => []
  | g :: gs => lookupCNF d gs ++ g.clauses (d + gs.length)

def lookupScoped (d : ℕ) : List LookupGate → Prop
  | [] => True
  | g :: gs => lookupScoped d gs ∧ g.wellScoped (d + gs.length)

def lookupValue (d : ℕ) (x : Assignment) : List LookupGate → Assignment
  | [] => x
  | g :: gs => fun i =>
    if i = d + gs.length then g.value (lookupValue d x gs) else lookupValue d x gs i

theorem lookupValue_input (d : ℕ) (x : Assignment) (gs : List LookupGate)
    {i : ℕ} (hi : i < d) : lookupValue d x gs i = x i := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simpa [lookupValue, show i ≠ d + gs.length by omega] using ih

private theorem cnf_append_eval (σ : Assignment) (a b : CNF) :
    CNF.eval σ (a ++ b) = true ↔ CNF.eval σ a = true ∧ CNF.eval σ b = true := by
  simp [CNF.eval]

theorem lookupCNF_eval (d : ℕ) (x σ : Assignment) (gs : List LookupGate)
    (hs : lookupScoped d gs) (hp : ∀ i < d, σ i = x i) :
    CNF.eval σ (lookupCNF d gs) = true ↔
      ∀ i < d + gs.length, σ i = lookupValue d x gs i := by
  induction gs with
  | nil => simpa [lookupCNF, lookupValue, CNF.eval] using hp
  | cons g gs ih =>
    change lookupScoped d gs ∧ g.wellScoped (d + gs.length) at hs
    rw [lookupCNF, cnf_append_eval, ih hs.1, g.clauses_eval]
    constructor
    · rintro ⟨hl, hz⟩ i hi
      simp only [lookupValue]
      split
      · rename_i he
        rw [he, hz, g.value_congr hs.2 hl]
      · exact hl i (by simp at hi; omega)
    · intro h
      have hl : ∀ i < d + gs.length, σ i = lookupValue d x gs i := by
        intro i hi
        simpa [lookupValue, show i ≠ d + gs.length by omega] using
          h i (by simp; omega)
      refine ⟨hl, ?_⟩
      rw [g.value_congr hs.2 hl]
      simpa [lookupValue] using h (d + gs.length) (by simp)

def lookupPins (d : ℕ) (x : Assignment) : CNF :=
  (List.range d).map fun i => [(i, x i)]

theorem lookupPins_eval (d : ℕ) (x σ : Assignment) :
    CNF.eval σ (lookupPins d x) = true ↔ ∀ i < d, σ i = x i := by
  simp [lookupPins, CNF.eval, Clause.eval, Literal.eval, List.all_eq_true]

theorem encodedCNF_mem_sat (φ : CNF) : encodeCNF φ ∈ SAT ↔ Satisfiable φ := by
  constructor
  · rintro ⟨ψ, he, h⟩
    exact (PEqualNP.Library.SearchHelpers.encodeCNF_injective he) ▸ h
  · intro h
    exact ⟨φ, rfl, h⟩

def lookupInstance (d : ℕ) (x : Assignment) (gs : List LookupGate) (out : ℕ) : CNF :=
  lookupPins d x ++ lookupCNF d gs ++ [[(out, true)]]

theorem lookupInstance_sat (d : ℕ) (x : Assignment) (gs : List LookupGate) (out : ℕ)
    (hs : lookupScoped d gs) (ho : out < d + gs.length) :
    encodeCNF (lookupInstance d x gs out) ∈ SAT ↔ lookupValue d x gs out = true := by
  rw [encodedCNF_mem_sat]
  change (∃ σ, CNF.eval σ (lookupInstance d x gs out) = true) ↔ _
  simp only [lookupInstance, cnf_append_eval, lookupPins_eval]
  have unit (σ : Assignment) : CNF.eval σ [[(out, true)]] = σ out := by
    simp [CNF.eval, Clause.eval, Literal.eval]
  constructor
  · rintro ⟨σ, ⟨hp, hg⟩, hout⟩
    rw [unit] at hout
    exact ((lookupCNF_eval d x σ gs hs hp).mp hg out ho).symm.trans hout
  · intro h
    let σ := lookupValue d x gs
    have hp : ∀ i < d, σ i = x i := fun _ hi => lookupValue_input d x gs hi
    exact ⟨σ, ⟨hp, (lookupCNF_eval d x σ gs hs hp).mpr (fun _ _ => rfl)⟩, (unit σ).trans h⟩

/-- Symbolic token layout. Only the one polarity per input pin is variable. -/
def lookupPinPattern (i : ℕ) : List (Bool ⊕ ℕ) :=
  [.inl true, .inr i] ++
    (i.bits.flatMap fun b => [.inl true, .inl b]) ++
    [.inl false, .inl true, .inl false, .inl false]

def lookupPattern (d : ℕ) (gs : List LookupGate) (out : ℕ) (pad : CNF) :
    List (Bool ⊕ ℕ) :=
  (List.range d).flatMap lookupPinPattern ++
    (encodeCNF (lookupCNF d gs ++ [[(out, true)]] ++ pad)).map Sum.inl

theorem lookupPattern_eval (d : ℕ) (x : Assignment) (gs : List LookupGate) (out : ℕ) (pad : CNF) :
    (lookupPattern d gs out pad).map (Sum.elim id x) =
      encodeCNF (lookupInstance d x gs out ++ pad) := by
  have pin (ids : List ℕ) : (ids.flatMap lookupPinPattern).map (Sum.elim id x) =
      encodeCNF (ids.map fun i => [(i, x i)]) := by
    simp [lookupPinPattern, encodeCNF,
    encodeClause, encodeLiteral, List.flatMap_map, List.map_flatMap,
      List.append_assoc]
  rw [lookupPattern, List.map_append, List.map_map, pin]
  simp [lookupInstance, lookupPins, encodeCNF, List.append_assoc]

theorem lookupPattern_inputs (d : ℕ) (gs : List LookupGate) (out : ℕ) (pad : CNF) :
    (lookupPattern d gs out pad).filterMap (fun
      | .inl _ => none
      | .inr i => some i) = List.range d := by
  let read : Bool ⊕ ℕ → Option ℕ := fun
    | .inl _ => none
    | .inr i => some i
  change (lookupPattern d gs out pad).filterMap read = List.range d
  have pin (ids : List ℕ) : (ids.flatMap lookupPinPattern).filterMap read = ids := by
    induction ids <;> simp_all [lookupPinPattern, read, List.filterMap_flatMap]
  simp [lookupPattern, pin, read]

private def lookupTautology (v : ℕ) : Clause := [(v, false), (v, true)]

private theorem lookupTautology_eval (v : ℕ) (x : Assignment) :
    Clause.eval x (lookupTautology v) = true := by
  cases h : x v <;> simp [lookupTautology, Clause.eval, Literal.eval, h]

private theorem replicate_clauses_length (a : ℕ) (c : Clause) :
    (encodeCNF (List.replicate a c)).length = a * (encodeClause c).length := by
  induction a with
  | zero => simp [encodeCNF]
  | succ a ih =>
    simp [encodeCNF, List.replicate_succ, Nat.succ_mul, Nat.add_comm] at ih ⊢

theorem lookupPadding (t : ℕ) (ht : 48 ≤ t) (he : t % 2 = 0) :
    ∃ pad : CNF, (encodeCNF pad).length = t ∧ ∀ x, CNF.eval x pad = true := by
  have hr : t % 10 = 0 ∨ t % 10 = 2 ∨ t % 10 = 4 ∨ t % 10 = 6 ∨ t % 10 = 8 := by omega
  obtain ⟨a, b, hab⟩ : ∃ a b : ℕ, 10*a + 14*b = t := by
    rcases hr with h | h | h | h | h
    · exact ⟨t/10, 0, by omega⟩
    · exact ⟨(t-42)/10, 3, by omega⟩
    · exact ⟨(t-14)/10, 1, by omega⟩
    · exact ⟨(t-56)/10, 4, by omega⟩
    · exact ⟨(t-28)/10, 2, by omega⟩
  let p := List.replicate a (lookupTautology 0)
  let q := List.replicate b (lookupTautology 1)
  refine ⟨p ++ q, ?_, ?_⟩
  · have hp : (encodeCNF p).length = a * 10 := replicate_clauses_length a (lookupTautology 0)
    have hq : (encodeCNF q).length = b * 14 := replicate_clauses_length b (lookupTautology 1)
    have eh : encodeCNF (p ++ q) = encodeCNF p ++ encodeCNF q := by simp [encodeCNF]
    rw [eh, List.length_append, hp, hq]
    omega
  · intro x
    simp [CNF.eval, p, q, lookupTautology_eval]

private theorem encodeCNF_even (φ : CNF) : (encodeCNF φ).length % 2 = 0 := by
  have digit (bs : List Bool) : (bs.flatMap fun b => [true, b]).length = 2 * bs.length := by
    induction bs with
    | nil => rfl
    | cons b bs ih => simp [ih]; omega
  have lits (c : Clause) : (c.flatMap encodeLiteral).length % 2 = 0 := by
    induction c with
    | nil => rfl
    | cons l ls ih =>
      simp [encodeLiteral, digit] at *
      omega
  induction φ with
  | nil => rfl
  | cons c cs ih =>
    have hc := lits c
    simp [encodeCNF, encodeClause] at *
    omega

theorem lookupPattern_padded (d : ℕ) (gs : List LookupGate) (out n : ℕ)
    (hs : lookupScoped d gs) (ho : out < d + gs.length)
    (hn : (lookupPattern d gs out []).length + 48 ≤ n) (he : n % 2 = 0) :
    ∃ pattern : List (Bool ⊕ ℕ), pattern.length = n ∧
      (pattern.filterMap fun | .inl _ => none | .inr i => some i) = List.range d ∧
      ∀ x : Assignment, (pattern.map (Sum.elim id x) ∈ SAT ↔ lookupValue d x gs out = true) := by
  have hl := congrArg List.length (lookupPattern_eval d (fun _ => false) gs out [])
  rw [List.length_map] at hl
  have he0 := encodeCNF_even (lookupInstance d (fun _ => false) gs out ++ [])
  obtain ⟨pad, hpad, ht⟩ := lookupPadding (n - (lookupPattern d gs out []).length)
    (by omega) (by omega)
  refine ⟨lookupPattern d gs out pad, ?_, lookupPattern_inputs d gs out pad, ?_⟩
  · have hlen : (lookupPattern d gs out pad).length =
        (lookupPattern d gs out []).length + (encodeCNF pad).length := by
      simp [lookupPattern, encodeCNF, List.flatMap_append]
      omega
    rw [hlen, hpad]
    omega
  · intro x
    rw [lookupPattern_eval, encodedCNF_mem_sat]
    have h : Satisfiable (lookupInstance d x gs out ++ pad) ↔
        Satisfiable (lookupInstance d x gs out) := by
      change (∃ σ, _) ↔ (∃ σ, _)
      simp [cnf_append_eval, ht]
    rw [h, ← encodedCNF_mem_sat, lookupInstance_sat d x gs out hs ho]

/-- Largest fitting member of a growing sequence, without a monotonicity hypothesis. -/
theorem lookupLength_select (L : ℕ → ℕ) (C n k₀ : ℕ)
    (grow : ∀ k, k ≤ L k) (ratio : ∀ k ≥ k₀, L (k + 1) ≤ C * L k)
    (fit : L k₀ + 48 ≤ n) :
    ∃ k ≥ k₀, L k + 48 ≤ n ∧ n < 48 + C * L k := by
  let fits : ℕ → Prop := fun k => L k + 48 ≤ n
  let : DecidablePred fits := fun k => inferInstanceAs (Decidable (L k + 48 ≤ n))
  let k := Nat.findGreatest fits n
  have h₀ : k₀ ≤ n := by have := grow k₀; omega
  have hk : fits k := Nat.findGreatest_spec h₀ fit
  have hlo : k₀ ≤ k := Nat.le_findGreatest h₀ fit
  have next : ¬ fits (k + 1) := by
    intro h
    have hb : k + 1 ≤ n := by
      have := grow (k + 1)
      dsimp [fits] at h
      omega
    have := Nat.le_findGreatest hb h
    omega
  have hrat := ratio k hlo
  dsimp [fits] at hk next
  exact ⟨k, hlo, hk, by omega⟩

private theorem clause_length_le (w : ℕ) (c : Clause) (hc : c.length ≤ 3)
    (h : ∀ l ∈ c, l.1 < 2 ^ w) : (encodeClause c).length ≤ 6 * w + 14 := by
  have lit (l : Literal) (hl : l.1 < 2 ^ w) : (encodeLiteral l).length ≤ 2*w+4 := by
    have bits (ds : List Bool) : (ds.flatMap fun b => [true, b]).length = 2 * ds.length := by
      induction ds with
      | nil => rfl
      | cons a as ih => simp [ih]; omega
    have hh := Nat.size_le.mpr hl
    simp [encodeLiteral, bits, Nat.size_eq_bits_len]
    omega
  have all (c : Clause) (h : ∀ l ∈ c, l.1 < 2 ^ w) :
      (c.flatMap encodeLiteral).length ≤ c.length * (2*w+4) := by
    induction c with
    | nil => simp
    | cons l ls ih =>
      have h₁ := lit l (h l (List.mem_cons_self ..))
      have h₂ := ih (fun a ha => h a (List.mem_cons_of_mem _ ha))
      simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.add_mul]
      omega
  have hproduct := Nat.mul_le_mul_right (2*w+4) hc
  simp only [encodeClause, List.length_append, List.length_cons, List.length_nil]
  have := all c h
  omega

private theorem lookupCNF_shape (d : ℕ) (gs : List LookupGate) (hs : lookupScoped d gs) :
    (lookupCNF d gs).length = 4 * gs.length ∧
      ∀ c ∈ lookupCNF d gs, c.length ≤ 3 ∧ ∀ l ∈ c, l.1 < d + gs.length := by
  induction gs with
  | nil => simp [lookupCNF]
  | cons g gs ih =>
    change lookupScoped d gs ∧ g.wellScoped (d+gs.length) at hs
    obtain ⟨ih₁, ih₂⟩ := ih hs.1
    constructor
    · simp only [lookupCNF, List.length_append, ih₁, List.length_cons]
      cases g <;> simp [LookupGate.clauses, Nat.mul_add]
    · intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · exact ⟨(ih₂ c hc).1, fun l hl => by
          have := (ih₂ c hc).2 l hl
          simp
          omega⟩
      · have now : ∀ c ∈ g.clauses (d+gs.length), c.length ≤ 3 ∧
            ∀ l ∈ c, l.1 < d + (g :: gs).length := by
          cases g with
          | xor a b =>
            have ha : a < d + gs.length + 1 := by have := hs.2.1; omega
            have hb : b < d + gs.length + 1 := by have := hs.2.2; omega
            simp only [LookupGate.clauses, List.mem_cons, List.not_mem_nil, or_false,
              List.length_cons]
            intro c hc
            rcases hc with rfl | rfl | rfl | rfl <;>
              simp [← Nat.add_assoc] <;> omega
          | mux s a b =>
            have ht : s < d + gs.length + 1 := by have := hs.2.1; omega
            have ha : a < d + gs.length + 1 := by have := hs.2.2.1; omega
            have hb : b < d + gs.length + 1 := by have := hs.2.2.2; omega
            simp only [LookupGate.clauses, List.mem_cons, List.not_mem_nil, or_false,
              List.length_cons]
            intro c hc
            rcases hc with rfl | rfl | rfl | rfl <;>
              simp [← Nat.add_assoc] <;> omega
        exact now c hc

theorem lookupPattern_length_le (d : ℕ) (gs : List LookupGate) (out w : ℕ)
    (hs : lookupScoped d gs) (ho : out < d + gs.length) (hw : d + gs.length ≤ 2 ^ w) :
    (lookupPattern d gs out []).length ≤ (d + 4 * gs.length + 1) * (6*w+14) := by
  let x : Assignment := fun _ => false
  let φ := lookupInstance d x gs out
  have hP := congrArg List.length (lookupPattern_eval d x gs out [])
  rw [List.length_map, List.append_nil] at hP
  obtain ⟨glen, gshape⟩ := lookupCNF_shape d gs hs
  have fl : φ.length = d + 4 * gs.length + 1 := by
    simp [φ, lookupInstance, lookupPins, glen, Nat.add_assoc]
  have enc (φ : CNF) (h : ∀ c ∈ φ, c.length ≤ 3 ∧ ∀ l ∈ c, l.1 < 2^w) :
      (encodeCNF φ).length ≤ φ.length * (6*w+14) := by
    induction φ with
    | nil => simp [encodeCNF]
    | cons c cs ih =>
      have h₁ := h c (List.mem_cons_self ..)
      have h₂ := clause_length_le w c h₁.1 h₁.2
      have h₃ := ih (fun c hc => h c (List.mem_cons_of_mem _ hc))
      simp only [encodeCNF, List.flatMap_cons, List.length_append, List.length_cons, Nat.add_mul] at *
      omega
  rw [hP, ← fl]
  apply enc φ
  intro c hc
  simp only [φ, lookupInstance, List.mem_append, List.mem_singleton] at hc
  rcases hc with (hp | hg) | rfl
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
    have hi' := List.mem_range.mp hi
    have hbound : i < 2 ^ w := by omega
    simp [hbound]
  · exact ⟨(gshape c hg).1, fun l hl => lt_of_lt_of_le ((gshape c hg).2 l hl) hw⟩
  · have hbound : out < 2 ^ w := ho.trans_le hw
    simp [hbound]

end SatBridge
