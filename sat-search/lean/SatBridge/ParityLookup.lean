import SatBridge.LookupProjection

/-! Certified compilation of a parity-addressed lookup with shared address wires. -/
namespace SatBridge
open PEqualNP.Search

private structure LookupBuilder (d : ℕ) where
  gates : List LookupGate
  scopedGates : lookupScoped d gates

private def LookupBuilder.bound {d : ℕ} (b : LookupBuilder d) : ℕ := d + b.gates.length

private structure LookupExtension {d : ℕ} (b : LookupBuilder d) where
  next : LookupBuilder d
  preserves : ∀ (x : Assignment) (i : ℕ), i < b.bound →
    lookupValue d x next.gates i = lookupValue d x b.gates i
  bound_le : b.bound ≤ next.bound

private def LookupExtension.refl {d : ℕ} (b : LookupBuilder d) : LookupExtension b :=
  ⟨b, fun _ _ _ => rfl, le_rfl⟩

private def LookupExtension.trans {d : ℕ} {b : LookupBuilder d} (e : LookupExtension b)
    (f : LookupExtension e.next) : LookupExtension b :=
  ⟨f.next, fun x i h => (f.preserves x i (lt_of_lt_of_le h e.bound_le)).trans (e.preserves x i h),
    e.bound_le.trans f.bound_le⟩

private structure LookupWire {d : ℕ} (b : LookupBuilder d) (f : Assignment → Bool) where
  id : ℕ
  inScope : id < b.bound
  evaluates : ∀ x, lookupValue d x b.gates id = f x

private def LookupExtension.lift {d : ℕ} {b : LookupBuilder d} (e : LookupExtension b)
    {f : Assignment → Bool} (w : LookupWire b f) : LookupWire e.next f :=
  ⟨w.id, lt_of_lt_of_le w.inScope e.bound_le, fun x =>
    (e.preserves x w.id w.inScope).trans (w.evaluates x)⟩

private def LookupBuilder.input {d : ℕ} (b : LookupBuilder d) (i : ℕ) (hi : i < d) :
    LookupWire b (fun x => x i) :=
  ⟨i, by unfold LookupBuilder.bound; omega, fun x => lookupValue_input d x b.gates hi⟩

private structure LookupBuilt {d : ℕ} (b : LookupBuilder d) (f : Assignment → Bool) (cost : ℕ) where
  extension : LookupExtension b
  result : LookupWire extension.next f
  cost_eq : extension.next.bound = b.bound + cost

private def LookupBuilder.emit {d : ℕ} (b : LookupBuilder d) (g : LookupGate)
    (h : g.wellScoped b.bound) {f : Assignment → Bool}
    (hv : ∀ x, g.value (lookupValue d x b.gates) = f x) : LookupBuilt b f 1 := by
  let b' : LookupBuilder d := ⟨g :: b.gates, b.scopedGates, h⟩
  have hb : b'.bound = b.bound + 1 := by simp [LookupBuilder.bound, b']; omega
  let ext : LookupExtension b := ⟨b', (by
    intro x i hi
    change (if i = b.bound then _ else _) = _
    rw [ite_eq_right (ne_of_lt hi)]), by omega⟩
  exact ⟨ext, ⟨b.bound, by change b.bound < b'.bound; omega, fun x => by
    change (if b.bound = b.bound then _ else _) = f x
    simpa using hv x⟩, hb⟩

private def LookupBuilder.xor {d : ℕ} {b : LookupBuilder d} {f g : Assignment → Bool}
    (a : LookupWire b f) (c : LookupWire b g) : LookupBuilt b (fun x => f x ^^ g x) 1 :=
  b.emit (.xor a.id c.id) ⟨a.inScope, c.inScope⟩ (fun x =>
    by simp [LookupGate.value, a.evaluates, c.evaluates])

private def LookupBuilder.mux {d : ℕ} {b : LookupBuilder d} {s f g : Assignment → Bool}
    (sel : LookupWire b s) (a : LookupWire b f) (c : LookupWire b g) :
    LookupBuilt b (fun x => if s x then g x else f x) 1 :=
  b.emit (.mux sel.id a.id c.id) ⟨sel.inScope, a.inScope, c.inScope⟩ (fun x =>
    by simp [LookupGate.value, sel.evaluates, a.evaluates, c.evaluates])

/-- Left-to-right parity of the input positions base through base + i inclusive. -/
def lookupRowParity (x : Assignment) (base : ℕ) : ℕ → Bool
  | 0 => x base
  | i + 1 => lookupRowParity x base i ^^ x (base + i + 1)

private def compileParity {d : ℕ} (b : LookupBuilder d) (base : ℕ) :
    (i : ℕ) → base + i < d → LookupBuilt b (fun x => lookupRowParity x base i) i
  | 0, h => ⟨.refl b, b.input base (by omega), by simp [LookupExtension.refl]⟩
  | i + 1, h =>
    let p := compileParity b base i (by omega)
    let last := p.extension.next.input (base + i + 1) (by omega)
    let q := p.extension.next.xor p.result last
    ⟨p.extension.trans q.extension, q.result, by
      simp only [LookupExtension.trans]
      rw [q.cost_eq, p.cost_eq, Nat.add_assoc]⟩

private inductive LookupSelectors {d : ℕ} (b : LookupBuilder d) :
    List (Assignment → Bool) → Type where
  | nil : LookupSelectors b []
  | cons {f fs} (w : LookupWire b f) (ws : LookupSelectors b fs) : LookupSelectors b (f :: fs)

private def LookupSelectors.lift {d : ℕ} {b : LookupBuilder d} (e : LookupExtension b) :
    {fs : List (Assignment → Bool)} → LookupSelectors b fs → LookupSelectors e.next fs
  | _, .nil => .nil
  | _, .cons w ws => .cons (e.lift w) (ws.lift e)

/-- Select a data position using the listed selectors, most significant first. -/
def lookupAddress (x : Assignment) : List (Assignment → Bool) → ℕ
  | [] => 0
  | f :: fs => (if f x then 2 ^ fs.length else 0) + lookupAddress x fs

private def compileMux {d : ℕ} {b : LookupBuilder d} (base : ℕ) :
    {fs : List (Assignment → Bool)} → LookupSelectors b fs →
    base + 2 ^ fs.length ≤ d → LookupBuilt b (fun x => x (base + lookupAddress x fs)) (2 ^ fs.length - 1)
  | [], .nil, h => ⟨.refl b, ⟨base, by unfold LookupBuilder.bound; simp at h; omega,
      fun x => by simpa [lookupAddress, LookupExtension.refl] using
        (lookupValue_input d x b.gates (i := base) (by simp at h; omega))⟩,
        by simp [LookupExtension.refl]⟩
  | f :: fs, .cons sel rest, h => by
    have hi : base + 2 ^ fs.length + 2 ^ fs.length ≤ d := by
      simpa [pow_succ, Nat.mul_two, Nat.add_assoc] using h
    let lo := compileMux base rest (Nat.le_trans (Nat.le_add_right _ _) hi)
    let hi := compileMux (base + 2 ^ fs.length) (rest.lift lo.extension) (by omega)
    let ext := lo.extension.trans hi.extension
    let p := hi.extension.next.mux (ext.lift sel) (hi.extension.lift lo.result) hi.result
    refine ⟨ext.trans p.extension, ⟨p.result.id, p.result.inScope, fun x => by
      simpa [lookupAddress, Nat.add_assoc, apply_ite (fun a : ℕ => a + lookupAddress x fs),
        apply_ite (fun a : ℕ => base + a), apply_ite x, LookupExtension.trans] using p.result.evaluates x⟩, ?_⟩
    change p.extension.next.bound = b.bound + _
    rw [p.cost_eq, hi.cost_eq, lo.cost_eq]
    have hpow : 0 < (2 : ℕ) ^ fs.length := by positivity
    simp only [List.length_cons, pow_succ, Nat.mul_two]
    omega
termination_by fs => fs.length

/-- First k selector rows of width r+1, most significant row first. -/
def lookupRows (m r : ℕ) : ℕ → List (Assignment → Bool)
  | 0 => []
  | k + 1 => (fun x => lookupRowParity x (m + k * (r + 1)) r) :: lookupRows m r k

private structure LookupBanks {d : ℕ} (b : LookupBuilder d) (fs : List (Assignment → Bool)) (cost : ℕ) where
  extension : LookupExtension b
  bank : LookupSelectors extension.next fs
  cost_eq : extension.next.bound = b.bound + cost

private def compileRows {d : ℕ} (b : LookupBuilder d) (m r : ℕ) :
    (k : ℕ) → m + k * (r + 1) ≤ d → LookupBanks b (lookupRows m r k) (k * r)
  | 0, _ => ⟨.refl b, .nil, by simp [LookupExtension.refl]⟩
  | k + 1, h => by
    have hh : m + k * (r + 1) + (r + 1) ≤ d := by simpa [Nat.succ_mul, Nat.add_assoc] using h
    let prior := compileRows b m r k (by omega)
    let latest := compileParity prior.extension.next (m + k * (r + 1)) r (by omega)
    refine ⟨prior.extension.trans latest.extension, .cons latest.result (prior.bank.lift latest.extension), ?_⟩
    change latest.extension.next.bound = b.bound + (k + 1) * r
    rw [latest.cost_eq, prior.cost_eq, Nat.succ_mul, Nat.add_assoc]

@[simp] theorem lookupRows_length (m r k : ℕ) : (lookupRows m r k).length = k := by
  induction k <;> simp [lookupRows, *]

/-- The data lookup specified by k parity rows of width r+1. -/
def parityLookup (k r : ℕ) (x : Assignment) : Bool :=
  x (lookupAddress x (lookupRows (2 ^ k) r k))

theorem parityLookup_program (k r : ℕ) :
    ∃ gs out, lookupScoped (2 ^ k + k * (r+1)) gs ∧ out < 2 ^ k + k * (r+1) + gs.length ∧
      gs.length = k * r + (2 ^ k - 1) ∧
      ∀ x, lookupValue (2 ^ k + k * (r+1)) x gs out = parityLookup k r x := by
  let m := 2 ^ k
  let d := m + k * (r+1)
  let start : LookupBuilder d := ⟨[], trivial⟩
  let rows := compileRows start m r k (le_refl d)
  let p := compileMux 0 rows.bank (by simp [d, m])
  refine ⟨p.extension.next.gates, p.result.id, p.extension.next.scopedGates, p.result.inScope, ?_, ?_⟩
  · have step := p.cost_eq
    rw [rows.cost_eq] at step
    have lengthEq : (2 : ℕ) ^ (lookupRows m r k).length = 2 ^ k := by simp
    have step' := calc
      p.extension.next.bound = start.bound + k*r + (2 ^ (lookupRows m r k).length - 1) := step
      _ = start.bound + k*r + (2 ^ k - 1) := by rw [lengthEq]
    clear step
    simp only [LookupBuilder.bound, start, List.length_nil, Nat.add_zero] at step'
    omega
  · intro x
    simpa [parityLookup, m] using p.result.evaluates x

theorem parityLookup_padded (k r : ℕ) :
    ∃ threshold, ∀ n ≥ threshold, n % 2 = 0 →
      ∃ pattern : List (Bool ⊕ ℕ), pattern.length = n ∧
        (pattern.filterMap fun | .inl _ => none | .inr i => some i) =
          List.range (2 ^ k + k * (r+1)) ∧
        ∀ x : Assignment, (pattern.map (Sum.elim id x) ∈ SAT ↔ parityLookup k r x = true) := by
  obtain ⟨gs, out, hs, ho, _, hv⟩ := parityLookup_program k r
  let d := 2 ^ k + k * (r+1)
  refine ⟨(lookupPattern d gs out []).length + 48, fun n h hn => ?_⟩
  obtain ⟨p, hl, hi, he⟩ := lookupPattern_padded d gs out n hs ho h hn
  exact ⟨p, hl, hi, fun x => (he x).trans (by rw [hv])⟩

/-- A convenient explicit bound on the number of bits in the unpadded projection. -/
def andreevLengthBudget (k : ℕ) : ℕ := 300 * (k+1) * 2 ^ k

/-- Embed the Andreev function with r=floor(2^k/k) whenever its length budget fits. -/
theorem andreev_padded (k n : ℕ) (hk : 0 < k)
    (hn : andreevLengthBudget k + 48 ≤ n) (he : n % 2 = 0) :
    ∃ pattern : List (Bool ⊕ ℕ), pattern.length = n ∧
      (pattern.filterMap fun | .inl _ => none | .inr i => some i) =
        List.range (2 ^ k + k * (2 ^ k / k)) ∧
      ∀ x : Assignment, (pattern.map (Sum.elim id x) ∈ SAT ↔
        parityLookup k (2 ^ k / k - 1) x = true) := by
  let m : ℕ := 2 ^ k
  let r := m/k
  have hpos : 0 < m := by dsimp [m]; positivity
  have hr : 0 < r := Nat.div_pos (Nat.le_of_lt (show k < 2^k from Nat.lt_two_pow_self)) hk
  have hkr : k*r ≤ m := by simpa [r, Nat.mul_comm] using Nat.div_mul_le_self m k
  obtain ⟨gs, out, hs, ho, hsize, hv⟩ := parityLookup_program k (r-1)
  let d := m+k*r
  have hr' : r - 1 + 1 = r := by omega
  simp only [hr'] at hs ho hv
  have hd : d ≤ 2*m := by dsimp [d]; omega
  have hq : gs.length < 2*m := by
    have hl := Nat.mul_le_mul_left k (Nat.sub_le r 1)
    change gs.length = k*(r-1)+(m-1) at hsize
    omega
  have hwidth : d + gs.length ≤ 2 ^ (k+2) := by
    rw [pow_add]
    change d + gs.length ≤ m*4
    omega
  have hlen := lookupPattern_length_le d gs out (k+2) hs ho hwidth
  have hcoeff : d + 4 * gs.length + 1 ≤ 11*m := by omega
  have hw : 6*(k+2)+14 ≤ 26*(k+1) := by omega
  have product := Nat.mul_le_mul hcoeff hw
  have htotal : (lookupPattern d gs out []).length ≤ andreevLengthBudget k := by
    apply hlen.trans (product.trans _)
    change 11*m*(26*(k+1)) ≤ 300*(k+1)*m
    calc
      _ = 286*(k+1)*m := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide))
  obtain ⟨p, hl, hi, heval⟩ := lookupPattern_padded d gs out n hs ho (by omega) he
  exact ⟨p, hl, hi, fun x => (heval x).trans (by rw [hv])⟩

/-- For all large even lengths choose a dimension on the correct exponential scale. -/
theorem andreev_padded_at_scale (n : ℕ) (hn : andreevLengthBudget 1 + 48 ≤ n)
    (he : n % 2 = 0) :
    ∃ k ≥ 1, andreevLengthBudget k + 48 ≤ n ∧ n < 48 + 4 * andreevLengthBudget k ∧
      ∃ pattern : List (Bool ⊕ ℕ), pattern.length = n ∧
        (pattern.filterMap fun | .inl _ => none | .inr i => some i) =
          List.range (2 ^ k + k * (2 ^ k / k)) ∧
        ∀ x : Assignment, (pattern.map (Sum.elim id x) ∈ SAT ↔
          parityLookup k (2 ^ k / k - 1) x = true) := by
  have grow (k : ℕ) : k ≤ andreevLengthBudget k := by
    have hm : 1 ≤ (2 : ℕ) ^ k := Nat.succ_le_of_lt (by positivity)
    have hh : 300*(k+1)*1 ≤ 300*(k+1)*2^k := Nat.mul_le_mul_left _ hm
    unfold andreevLengthBudget
    omega
  have ratio (k : ℕ) (_ : k ≥ 1) : andreevLengthBudget (k+1) ≤ 4*andreevLengthBudget k := by
    unfold andreevLengthBudget
    rw [pow_succ]
    calc
      300*(k+1+1)*(2^k*2) = (600*(k+2))*2^k := by ring
      _ ≤ (1200*(k+1))*2^k := Nat.mul_le_mul_right _ (by omega)
      _ = 4*(300*(k+1)*2^k) := by ring
  obtain ⟨k, hk, hfit, hscale⟩ := lookupLength_select andreevLengthBudget 4 n 1 grow ratio hn
  exact ⟨k, hk, hfit, hscale, andreev_padded k n (by omega) hfit he⟩

end SatBridge
