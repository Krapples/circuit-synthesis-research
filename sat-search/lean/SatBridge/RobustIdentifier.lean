import SatBridge.IdentifierLayout
import SatBridge.RobustRestriction
import CircuitLemmas.PairSensitiveCounting

namespace SatBridge

open PEqualNP.Search CircuitLemmas.GateElim

private def digitEmbedding (r p j : ℕ) : ℕ ↪ ℕ :=
  ⟨fun i => p + j * (2 + r * 2 + 6) + identifierOffset i, by
    intro a b h
    dsimp [identifierOffset] at h
    omega⟩

private theorem helper_length (r : ℕ) (rows : List (Fin r → Bool)) :
    (encodeCNF (unitCNF (rows.map fun row => identifier (List.ofFn row)) [] [])).length =
      rows.length * (2 + r * 2 + 6) := by
  induction rows with
  | nil => simp [encodeCNF, unitCNF]
  | cons row rows ih =>
    have h := encode_identifier_unit_length (List.ofFn row) false
    simp only [List.length_ofFn] at h
    simp only [unitCNF, List.map_nil, List.append_nil, encodeCNF] at ih
    simp only [unitCNF, List.map_nil, List.append_nil, List.map_cons,
      encodeCNF, List.flatMap_cons, List.length_append, h, ih, List.length_cons, Nat.add_mul]
    omega

/-- The robust identifier bound at lengths divisible by six, with an explicit budget for the
helper clauses, positive queries, and padding. -/
theorem sat_robust_identifier_lower {Q k r d : ℕ} (hQ : 1 ≤ Q) (hk : 0 < k)
    (hd : 2 ≤ d) (hdr : d ≤ r)
    (hcount : 3 ^ r * r * r * 2 < 2 ^ (2 ^ (d - 2)))
    (hfit : (2 ^ r + k) * (2 + r * 2 + 6) + 6 ≤ 6 * (Q + 1))
    (D : PEqualNP.CircuitLowerBounds.Circuit)
    (hD : ∀ g ∈ D.gates, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} :
        Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2)
    (hdec : D.Decides SAT (6 * (Q + 1))) :
    6 * (Q + 1) + k * (2 * r + 3 - 3 * d) ≤ D.size := by
  classical
  let n := 6 * (Q + 1)
  let L := 2 + r * 2 + 6
  obtain ⟨φ, hdep, hps⟩ := exists_PS (Finset.range r) d (by simpa using hdr)
    (by simpa using hcount)
  let test (row : Fin r → Bool) := φ (fun i => if h : i < r then row ⟨i, h⟩ else false)
  let rows : List (Fin r → Bool) := Finset.univ.toList
  let bad := rows.filter fun row => !test row
  let ident (row : Fin r → Bool) := identifier (List.ofFn row)
  let pre := encodeCNF (unitCNF (bad.map ident) [] [])
  have hpre : pre.length = bad.length * L := helper_length r bad
  have hbad : bad.length ≤ 2 ^ r := by
    calc
      bad.length ≤ rows.length := List.length_filter_le _ _
      _ = 2 ^ r := by simp [rows]
  have hfit' : pre.length + k * L + 6 ≤ n := by
    rw [hpre, ← Nat.add_mul]
    exact (Nat.add_le_add_right (Nat.mul_le_mul_right L (Nat.add_le_add_right hbad k)) 6).trans hfit
  let t := n - (pre.length + k * L)
  have htle : 6 ≤ t := by dsimp [t]; omega
  have hte : t % 2 = 0 := by
    dsimp [t, n]
    rw [hpre]
    have hL : L = 2 * (r + 4) := by dsimp [L]; omega
    rw [← Nat.add_mul, hL, ← Nat.mul_assoc, Nat.mul_comm (bad.length + k) 2, Nat.mul_assoc]
    have hN : 6 * (Q + 1) = 2 * (3 * (Q + 1)) := by omega
    rw [hN, ← Nat.mul_sub]
    simp
  obtain ⟨pad, hpad, hlen⟩ := exists_unit_padding t hte htle
  let suffix := encodeCNF (unitCNF [] [] pad)
  let F := queryFixed pre suffix r k
  let e := digitEmbedding r pre.length
  let V := queryBlock r pre.length
  let factors (j : ℕ) (x : ℕ → Bool) := φ (x ∘ e j)
  have hn : pre.length + k * L + suffix.length = n := by
    change suffix.length = t at hlen
    dsimp [t] at hlen
    omega
  have hmap (j : ℕ) : (Finset.range r).map (e j) = V j := by
    rw [Finset.map_eq_image]
    rfl
  have hfactor (j : ℕ) : DepOn (V j) (factors j) ∧ PS d (V j) (factors j) := by
    rw [← hmap]
    exact pairSensitive_reindex hdep hps (e j)
  have hFn : ∀ w ∈ F, w < n := by
    intro w hw
    rw [← hn]
    exact Finset.mem_range.mp (Finset.mem_sdiff.mp hw).1
  have hVn : ∀ j < k, ∀ w ∈ V j, w < n := by
    intro j hj w hw
    rw [← hn]
    exact queryBlock_lt (s := suffix.length) hj hw
  have hsize : F.card + k * r = n := (queryFixed_card_add pre suffix r k).trans hn
  have hword (x : ℕ → Bool) :
      (List.ofFn fun i : Fin n =>
        fixS F (queryLayoutBit pre suffix r k (fun _ => false)) x i) ∈ SAT ↔
        prodP k factors x = true := by
    let query (j : Fin k) (i : Fin r) := x (e j i)
    let queries := List.ofFn query
    have hw : (List.ofFn fun i : Fin n =>
        fixS F (queryLayoutBit pre suffix r k (fun _ => false)) x i) =
        encodeCNF (unitCNF (bad.map ident) (queries.map ident) pad) := by
      rw [List.ofFn_congr hn.symm]
      have he : (fun i : Fin (pre.length + k * L + suffix.length) =>
          fixS F (queryLayoutBit pre suffix r k (fun _ => false)) x i) =
          (fun i : Fin (pre.length + k * L + suffix.length) => queryLayoutBit pre suffix r k x i) := by
        funext i
        exact queryLayout_fix pre suffix r k x i.isLt
      simp only [Fin.val_cast, he]
      rw [queryLayout_word]
      simp [pre, suffix, unitCNF, encodeCNF, queries, query, ident, e, digitEmbedding,
        List.flatMap, List.map_ofFn, Function.comp_def,
        List.append_assoc]
      rfl
    rw [hw, unitCNF_table_mem_sat rows queries test ident pad (fun _ => by simp [rows])]
    · simp only [queries, List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff,
        prodP, List.all_eq_true, List.mem_range]
      constructor
      · intro h j hj
        have he : test (query ⟨j, hj⟩) = factors j x := by
          apply hdep
          intro i hi
          simp [query, Finset.mem_range.mp hi]
        exact he ▸ h ⟨j, hj⟩
      · intro h j
        have he : test (query j) = factors j x := by
          apply hdep
          intro i hi
          simp [query, Finset.mem_range.mp hi]
        exact he.symm ▸ h j j.isLt
    · intro a b hab
      exact List.ofFn_injective (identifier_injective hab)
    · intro v hv row
      exact padding_ne_identifier (List.ofFn row) (by simpa using hd.trans hdr) (hpad v hv)
  exact sat_robust_restriction_lower hQ hk hd hdr D hD hdec V factors F
    (queryLayoutBit pre suffix r k (fun _ => false)) hVn
    (fun i _ j _ h => queryBlock_disjoint r pre.length i j h)
    (fun j _ => (hfactor j).1) (fun j _ => (hfactor j).2)
    (fun j _ => queryBlock_card r pre.length j) hFn hsize hword

/-- An explicit numeric bound with a logarithmic threshold and the maximum block count under
the conservative allowance of 2^r helper clauses and one extra clause length. -/
theorem sat_robust_identifier_numeric {Q r : ℕ} (hQ : 1 ≤ Q) (hr : 8 ≤ r)
    (hfit : 2 ^ r + 2 ≤ (6 * (Q + 1)) / (2 + r * 2 + 6))
    (D : PEqualNP.CircuitLowerBounds.Circuit)
    (hD : ∀ g ∈ D.gates, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} :
        Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2)
    (hdec : D.Decides SAT (6 * (Q + 1))) :
    let n := 6 * (Q + 1)
    let k := n / (2 + r * 2 + 6) - 2 ^ r - 1
    n + k * (2 * r + 3 - 3 * (Nat.log2 r + 5)) ≤ D.size := by
  let n := 6 * (Q + 1)
  let L := 2 + r * 2 + 6
  let k := n / L - 2 ^ r - 1
  change 2 ^ r + 2 ≤ n / L at hfit
  change n + k * (2 * r + 3 - 3 * (Nat.log2 r + 5)) ≤ D.size
  have hk : 0 < k := by dsimp only [k]; omega
  have hdiv : n / L = 2 ^ r + k + 1 := by dsimp only [k]; omega
  have hn := Nat.div_mul_le_self n L
  rw [hdiv, Nat.add_mul, Nat.one_mul] at hn
  have hL : 6 ≤ L := by dsimp [L]; omega
  have hfit' : (2 ^ r + k) * L + 6 ≤ n := by omega
  obtain ⟨hd, hdr, hc⟩ := pairSensitive_logarithmic_parameters hr
  exact sat_robust_identifier_lower hQ hk hd hdr hc hfit' D hD hdec

/-- Separate the loss below 2n into the per-block threshold and the space for helpers and padding. -/
theorem sat_robust_identifier_loss {Q r : ℕ} (hQ : 1 ≤ Q) (hr : 8 ≤ r)
    (hfit : 2 ^ r + 2 ≤ (6 * (Q + 1)) / (2 + r * 2 + 6))
    (D : PEqualNP.CircuitLowerBounds.Circuit)
    (hD : ∀ g ∈ D.gates, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} :
        Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2)
    (hdec : D.Decides SAT (6 * (Q + 1))) :
    let n := 6 * (Q + 1)
    let L := 2 + r * 2 + 6
    2 * n ≤ D.size + (n / L) * (3 * (Nat.log2 r + 5) + 5) + (2 ^ r + 2) * L := by
  let n := 6 * (Q + 1)
  let L := 2 + r * 2 + 6
  let d := Nat.log2 r + 5
  let k := n / L - 2 ^ r - 1
  let A := 2 * r + 3 - 3 * d
  let B := 3 * d + 5
  change 2 ^ r + 2 ≤ n / L at hfit
  change 2 * n ≤ D.size + (n / L) * B + (2 ^ r + 2) * L
  have hbound : n + k * A ≤ D.size := sat_robust_identifier_numeric hQ hr hfit D hD hdec
  have hL : L ≤ A + B := by dsimp [L, A, B]; omega
  have hblock : k * L ≤ k * A + k * B :=
    (Nat.mul_le_mul_left k hL).trans_eq (Nat.mul_add k A B)
  have hdiv : n / L = k + (2 ^ r + 1) := by dsimp only [k]; omega
  have hrem := Nat.mod_lt n (show 0 < L by dsimp [L]; omega)
  have he : k * L + (2 ^ r + 1) * L + n % L = n := calc
    _ = (k + (2 ^ r + 1)) * L + n % L := by rw [Nat.add_mul k (2 ^ r + 1) L]
    _ = (n / L) * L + n % L := by rw [← hdiv]
    _ = n := by simpa only [Nat.mul_comm L] using Nat.div_add_mod n L
  have hpad : (2 ^ r + 2) * L = (2 ^ r + 1) * L + L := by
    rw [show 2 ^ r + 2 = (2 ^ r + 1) + 1 by omega, Nat.add_mul, Nat.one_mul]
  have hk : k ≤ n / L := (Nat.sub_le (n / L - 2 ^ r) 1).trans (Nat.sub_le (n / L) (2 ^ r))
  have hthreshold := Nat.mul_le_mul_right B hk
  omega

/-- An explicit loss bound with the logarithmic block width already chosen from the SAT length. -/
theorem sat_robust_identifier_logarithmic_width {Q : ℕ} (hQ : 1 ≤ Q)
    (hN : 2 ^ 16 ≤ 6 * (Q + 1)) (D : PEqualNP.CircuitLowerBounds.Circuit)
    (hD : ∀ g ∈ D.gates, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} :
        Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2)
    (hdec : D.Decides SAT (6 * (Q + 1))) :
    let n := 6 * (Q + 1)
    let r := n.log2 / 2
    let L := 2 + r * 2 + 6
    2 * n ≤ D.size + (n / L) * (3 * (Nat.log2 r + 5) + 5) + (2 ^ r + 2) * L := by
  let n := 6 * (Q + 1)
  let r := n.log2 / 2
  let L := 2 + r * 2 + 6
  have hn : n ≠ 0 := by dsimp [n]; omega
  have hlog : 16 ≤ n.log2 := (Nat.le_log2 hn).mpr hN
  have hr : 8 ≤ r := by dsimp [r]; omega
  have hlinear (t : ℕ) : 2 + (8 + t) * 2 + 6 ≤ 2 ^ (7 + t) := by
    induction t with
    | zero => decide
    | succ t ih =>
      rw [show 7 + (t + 1) = (7 + t) + 1 by omega, pow_succ]
      omega
  have hL : L ≤ 2 ^ (r - 1) := by
    have h := hlinear (r - 8)
    rw [show 8 + (r - 8) = r by omega, show 7 + (r - 8) = r - 1 by omega] at h
    exact h
  have hpow : (2 : ℕ) ^ 1 ≤ 2 ^ r :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (show 1 ≤ r by omega)
  have hfit : 2 ^ r + 2 ≤ n / L := (Nat.le_div_iff_mul_le (by dsimp [L]; omega)).mpr (calc
    (2 ^ r + 2) * L ≤ (2 ^ r + 2 ^ r) * 2 ^ (r - 1) := Nat.mul_le_mul (by omega) hL
    _ = 2 ^ (r + r) := by
      rw [← Nat.two_mul, ← Nat.pow_succ', ← pow_add, show r + 1 + (r - 1) = r + r by omega]
    _ ≤ 2 ^ n.log2 := Nat.pow_le_pow_right (by decide) (by dsimp [r]; omega)
    _ ≤ n := Nat.log2_self_le hn)
  exact sat_robust_identifier_loss hQ hr hfit D hD hdec

/-- For every reciprocal integer error tolerance, the corresponding slope below two
holds at all sufficiently large lengths divisible by six. -/
theorem sat_robust_identifier_eventually (m : ℕ) (hm : 0 < m) :
    ∃ N : ℕ, ∀ Q, 1 ≤ Q → N ≤ 6 * (Q + 1) →
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
      (∀ g ∈ D.gates, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
        PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} :
          Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2) →
      D.Decides SAT (6 * (Q + 1)) → 2 * m * (6 * (Q + 1)) ≤ m * D.size + 6 * (Q + 1) := by
  let s := 40 * m
  let r := 2 ^ (s + s)
  let L := 2 + r * 2 + 6
  let B := 3 * (Nat.log2 r + 5) + 5
  let H := (2 ^ r + 2) * L
  have hL : 0 < L := by dsimp [L]; omega
  have hr : 8 ≤ r := by
    change 2 ^ 3 ≤ 2 ^ (s + s)
    exact Nat.pow_le_pow_right (by decide) (by dsimp [s]; omega)
  have hrLarge : (s + 1) * (s + 1) ≤ r := by
    have hs : s + 1 ≤ 2 ^ s := Nat.lt_two_pow_self
    simpa only [r, pow_add] using Nat.mul_le_mul hs hs
  have hscale : 2 * m * B ≤ L := by
    have hB : B = 6 * s + 20 := by dsimp [B, r]; rw [Nat.log2_two_pow]; omega
    have hsmall : 2 * m * (6 * s + 20) ≤ 2 * ((s + 1) * (s + 1)) := by
      dsimp [s]
      nlinarith
    rw [hB]
    have hlarge := Nat.mul_le_mul_left 2 hrLarge
    dsimp only [L]
    omega
  refine ⟨2 * m * H, ?_⟩
  intro Q hQ hN D hD hdec
  let n := 6 * (Q + 1)
  change 2 * m * H ≤ n at hN
  change 2 * m * n ≤ m * D.size + n
  have hHmul : H ≤ 2 * m * H := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right H (show 1 ≤ 2 * m by omega)
  have hHn : H ≤ n := hHmul.trans hN
  have hfit : 2 ^ r + 2 ≤ n / L := (Nat.le_div_iff_mul_le hL).mpr hHn
  have hbound : 2 * n ≤ D.size + (n / L) * B + H :=
    sat_robust_identifier_loss hQ hr hfit D hD hdec
  have hBhalf : 2 * m * ((n / L) * B) ≤ n := calc
    _ = (n / L) * (2 * m * B) := by ring
    _ ≤ (n / L) * L := Nat.mul_le_mul_left _ hscale
    _ ≤ n := Nat.div_mul_le_self _ _
  have hscaled := Nat.mul_le_mul_left (2 * m) hbound
  simp only [Nat.mul_add] at hscaled
  rw [show 2 * m * (2 * n) = 2 * (2 * m * n) by ring,
    show 2 * m * D.size = 2 * (m * D.size) by ring] at hscaled
  omega

end SatBridge
