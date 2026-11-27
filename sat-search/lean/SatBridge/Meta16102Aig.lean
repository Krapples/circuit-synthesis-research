/-
**Gap (A) of L-meta-16102 in Lean: `C(f16102) ≥ 8` in the free-NOT AIG model (2026-11-26).**

This discharges the hypothesis `hA : ¬ Realizes 6 F 7` of `SatBridge.Meta16102.posted_core`.

The proof is the first-gate recursion of `sat-search/results/mid_not_16102/aig8_recursion_proof.md`.
`CircuitLemmas.GateElim.FirstGate.first_gate` gives the facts that fixing a first-gate input deletes gates.
This file checks a finite certificate (`Meta16102AigData.entries`, 95 truth tables) against those facts by
`decide +kernel`, and proves the checker sound by strong induction on the gate count.

Tables are natural numbers: bit `k` of `tt` is the value at `pt k`, whose input `w` is bit `w` of `k`.
-/
import CircuitLemmas.FirstGate
import SatBridge.Meta16102
import SatBridge.Meta16102AigData

namespace SatBridge.Meta16102Aig

open CircuitLemmas.GateElim CircuitLemmas.GateElim.FirstGate

/-! ## Tables -/

def b2n (b : Bool) : ℕ := if b then 1 else 0

def idxB (b0 b1 b2 b3 b4 b5 : Bool) : ℕ :=
  b2n b0 + 2 * b2n b1 + 4 * b2n b2 + 8 * b2n b3 + 16 * b2n b4 + 32 * b2n b5

def idx (x : ℕ → Bool) : ℕ := idxB (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

def pt (k : ℕ) : ℕ → Bool := fun w => k.testBit w

/-- The function with table `tt`. -/
def T (tt : ℕ) (x : ℕ → Bool) : Bool := tt.testBit (idx x)

theorem idxB_spec : ∀ b0 b1 b2 b3 b4 b5 : Bool, idxB b0 b1 b2 b3 b4 b5 < 64 ∧
    (idxB b0 b1 b2 b3 b4 b5).testBit 0 = b0 ∧ (idxB b0 b1 b2 b3 b4 b5).testBit 1 = b1 ∧
    (idxB b0 b1 b2 b3 b4 b5).testBit 2 = b2 ∧ (idxB b0 b1 b2 b3 b4 b5).testBit 3 = b3 ∧
    (idxB b0 b1 b2 b3 b4 b5).testBit 4 = b4 ∧ (idxB b0 b1 b2 b3 b4 b5).testBit 5 = b5 := by
  decide +kernel

theorem idx_lt (x : ℕ → Bool) : idx x < 64 := (idxB_spec ..).1

theorem pt_idx (x : ℕ → Bool) (w : ℕ) (hw : w < 6) : pt (idx x) w = x w := by
  obtain ⟨-, h0, h1, h2, h3, h4, h5⟩ := idxB_spec (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)
  simp only [pt, idx]
  interval_cases w <;> assumption

theorem idx_pt : ∀ k < 64, idx (pt k) = k := by decide +kernel

theorem idx_congr {x y : ℕ → Bool} (h : ∀ w < 6, x w = y w) : idx x = idx y := by
  simp only [idx, h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num),
    h 4 (by norm_num), h 5 (by norm_num)]

/-- Two functions of `x_0, …, x_5` that agree on the 64 points agree everywhere. -/
theorem agree (G H : (ℕ → Bool) → Bool) (hG : ∀ x y, (∀ w < 6, x w = y w) → G x = G y)
    (hH : ∀ x y, (∀ w < 6, x w = y w) → H x = H y) (hp : ∀ k < 64, G (pt k) = H (pt k))
    (x : ℕ → Bool) : G x = H x := by
  have hx : ∀ w < 6, x w = pt (idx x) w := fun w hw => (pt_idx x w hw).symm
  rw [hG x _ hx, hH x _ hx]
  exact hp _ (idx_lt x)

theorem T_congr (tt : ℕ) : ∀ x y, (∀ w < 6, x w = y w) → T tt x = T tt y := fun _ _ h => by
  simp only [T, idx_congr h]

theorem T_pt (tt k : ℕ) (hk : k < 64) : T tt (pt k) = tt.testBit k := by simp only [T, idx_pt k hk]

/-! ## The checker -/

/-- `r` is the table of `x_v := b` applied to `tt`. -/
def rok (tt v : ℕ) (b : Bool) (r : ℕ) : Bool :=
  (List.range 64).all fun k => r.testBit k == T tt (upd (pt k) v b)

def look (L : List E) (tt : ℕ) : ℕ := ((L.find? fun e => e.tt == tt).map E.lb).getD 0

def ncB (t : ℕ) : Bool := (List.range 64).any fun k => t.testBit k != t.testBit 0

def ri (e : E) (v : ℕ) (b : Bool) : ℕ := e.rs.getD (2 * v + b2n b) 0
def ci (e : E) (v : ℕ) (b : Bool) : ℕ := e.cs.getD (2 * v + b2n b) 0
def ni (e : E) (v : ℕ) (b : Bool) : Bool := e.ns.getD (2 * v + b2n b) false

/-- The stored restrictions, their bounds and their constancy flags are right. -/
def okR (L : List E) (e : E) : Bool := (List.range 6).all fun v => [false, true].all fun b =>
  rok e.tt v b (ri e v b) && ci e v b == look L (ri e v b) && ni e v b == ncB (ri e v b)

/-- The bound from first-gate input `v` (controlling value `bv`) in reader class `0` (one reader),
`1` (two, the second controlled by `!bv`), `2` (two, both controlled by `bv`) or `3` (three or more). -/
def fact (e : E) (v : ℕ) (bv : Bool) : ℕ → ℕ
  | 0 => max (2 + ci e v bv) (1 + ci e v (!bv))
  | 1 => max (max (2 + max (ci e v false) (ci e v true)) (3 + ci e v bv))
      ((if ni e v (!bv) then 3 else 2) + ci e v (!bv))
  | 2 => max (max (2 + max (ci e v false) (ci e v true)) (3 + ci e v bv))
      ((if ni e v bv then 4 else 3) + ci e v bv)
  | _ => 3 + max (ci e v false) (ci e v true)

def minL (l : List ℕ) : ℕ := l.foldr min 1000

/-- The bound for first gate `x_i^ai ∧ x_j^aj`; class pair `(0, 0)` needs the factor flag `fl`. -/
def pairB (e : E) (i j : ℕ) (ai aj fl : Bool) : ℕ :=
  minL ((List.range 4).flatMap fun a => (List.range 4).map fun b =>
    if a = 0 ∧ b = 0 ∧ fl = false then 1000 else max (fact e i ai a) (fact e j aj b))

/-- `tt` sees `x_i, x_j` only through `x_i^ai ∧ x_j^aj` (tested where that gate is false). -/
def factB (tt i j : ℕ) (ai aj : Bool) : Bool := (List.range 64).all fun k =>
  (T tt (upd (upd (pt k) i ai) j aj) == T tt (upd (upd (pt k) i ai) j (!aj))) &&
  (T tt (upd (upd (pt k) i ai) j aj) == T tt (upd (upd (pt k) i (!ai)) j aj))

def notLitB (tt : ℕ) : Bool :=
  [false, true].all (fun c => (List.range 64).any fun k => T tt (pt k) != c) &&
  (List.range 6).all fun u => [false, true].all fun neg =>
    (List.range 64).any fun k => T tt (pt k) != (pt k u ^^ neg)

def notGateB (tt : ℕ) : Bool := (List.range 6).all fun i => (List.range 6).all fun j => i == j ||
  [false, true].all fun ai => [false, true].all fun aj => [false, true].all fun neg =>
    (List.range 64).any fun k => T tt (pt k) != (((pt k i ^^ ai) && (pt k j ^^ aj)) ^^ neg)

def okPair (e : E) (i j : ℕ) (ai aj : Bool) : Bool :=
  decide (e.lb ≤ pairB e i j ai aj true) || decide (e.lb ≤ pairB e i j ai aj (factB e.tt i j ai aj))

def okE (L : List E) (e : E) : Bool :=
  e.lb == 0 || (notLitB e.tt && (e.lb == 1 || (notGateB e.tt && okR L e &&
    (List.range 6).all fun i => (List.range 6).all fun j => i == j ||
      [false, true].all fun ai => [false, true].all fun aj => okPair e i j ai aj)))

def checkAll (L : List E) : Bool := L.all (okE L)

/-! ## Soundness -/

theorem bools {p : Bool → Bool} (h : [false, true].all p = true) (b : Bool) : p b = true := by
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  cases b
  exacts [h.1, h.2]

theorem rng {n : ℕ} {p : ℕ → Bool} (h : (List.range n).all p = true) (k : ℕ) (hk : k < n) :
    p k = true := List.all_eq_true.1 h k (List.mem_range.2 hk)

theorem rngAny {n : ℕ} {p : ℕ → Bool} (h : (List.range n).any p = true) : ∃ k < n, p k = true := by
  obtain ⟨k, hk, h⟩ := List.any_eq_true.1 h
  exact ⟨k, List.mem_range.1 hk, h⟩

theorem rok_sound (tt v : ℕ) (b : Bool) (r : ℕ) (h : rok tt v b r = true) (x : ℕ → Bool) :
    T tt (upd x v b) = T r x := by
  refine agree (fun x => T tt (upd x v b)) (T r) (fun x y hxy => T_congr tt _ _ fun w hw => ?_)
    (T_congr r) (fun k hk => ?_) x
  · simp only [upd]
    split_ifs
    · rfl
    · exact hxy w hw
  · simp only [rok, List.all_eq_true, List.mem_range, beq_iff_eq] at h
    rw [T_pt r k hk, h k hk]

theorem minL_le (l : List ℕ) (a : ℕ) (h : a ∈ l) : minL l ≤ a := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
      rcases List.mem_cons.1 h with rfl | h
      · simp only [minL, List.foldr]; omega
      · have := ih h
        simp only [minL, List.foldr] at this ⊢
        omega

theorem pairB_le (e : E) (i j : ℕ) (ai aj fl : Bool) (a b : ℕ) (ha : a < 4) (hb : b < 4)
    (hf : a = 0 → b = 0 → fl = true) :
    pairB e i j ai aj fl ≤ max (fact e i ai a) (fact e j aj b) := by
  have hmem : (if a = 0 ∧ b = 0 ∧ fl = false then 1000 else max (fact e i ai a) (fact e j aj b)) ∈
      ((List.range 4).flatMap fun a => (List.range 4).map fun b =>
        if a = 0 ∧ b = 0 ∧ fl = false then 1000 else max (fact e i ai a) (fact e j aj b)) := by
    simp only [List.mem_flatMap, List.mem_map, List.mem_range]
    exact ⟨a, ha, b, hb, rfl⟩
  have := minL_le _ _ hmem
  rw [if_neg (by rintro ⟨h1, h2, h3⟩; simp [hf h1 h2] at h3)] at this
  exact this

theorem factB_of (tt i j : ℕ) (ai aj : Bool) (hij : i ≠ j)
    (hf : ∀ x y, (∀ w, w ≠ i → w ≠ j → x w = y w) →
      ((x i ^^ ai) && (x j ^^ aj)) = ((y i ^^ ai) && (y j ^^ aj)) → T tt x = T tt y) :
    factB tt i j ai aj = true := by
  simp only [factB, List.all_eq_true, Bool.and_eq_true, beq_iff_eq]
  intro k _
  exact ⟨hf _ _ (fun w hwi hwj => by simp [upd, hwi, hwj]) (by simp [upd, hij]),
    hf _ _ (fun w hwi hwj => by simp [upd, hwi, hwj]) (by simp [upd, hij])⟩

theorem notLit_sound (tt : ℕ) (h : notLitB tt = true) :
    (∀ c, ¬ ∀ x, T tt x = c) ∧ ∀ u < 6, ∀ neg, ¬ ∀ x, T tt x = (x u ^^ neg) := by
  simp only [notLitB, Bool.and_eq_true] at h
  refine ⟨fun c hc => ?_, fun u hu neg hc => ?_⟩
  · obtain ⟨k, -, hk⟩ := rngAny (bools h.1 c)
    simp [hc] at hk
  · obtain ⟨k, -, hk⟩ := rngAny (bools (rng h.2 u hu) neg)
    simp [hc] at hk

theorem notGate_sound (tt : ℕ) (h : notGateB tt = true) (i j : ℕ) (hij : i ≠ j) (hi : i < 6)
    (hj : j < 6) (ai aj neg : Bool) :
    ¬ ∀ x, T tt x = (((x i ^^ ai) && (x j ^^ aj)) ^^ neg) := by
  have := rng (rng h i hi) j hj
  simp only [Bool.or_eq_true, beq_iff_eq] at this
  rcases this with h' | h'
  · exact absurd h' hij
  obtain ⟨k, -, hk⟩ := rngAny (bools (bools (bools h' ai) aj) neg)
  intro hc
  simp [hc] at hk

/-- The facts of one first-gate input give one of the checker's class bounds. -/
theorem fact_le (L : List E) (e : E) (hR : okR L e = true) (S s : ℕ) (hS : S ≤ s)
    (ih : ∀ m < s, ∀ tt, Realizes 6 (T tt) m → look L tt ≤ m) (v : ℕ) (hv : v < 6) (bv : Bool)
    (r : ℕ) (hF : Facts 6 (T e.tt) S v bv r) :
    ∃ a < 4, (a = 0 → r = 1) ∧ fact e v bv a ≤ S := by
  have hchk : ∀ b, rok e.tt v b (ri e v b) = true ∧ ci e v b = look L (ri e v b) ∧
      ni e v b = ncB (ri e v b) := fun b => by
    have := bools (rng hR v hv) b
    simpa only [Bool.and_eq_true, beq_iff_eq, and_assoc] using this
  have hCB : ∀ b k, RLe 6 (fun x => T e.tt (upd x v b)) S k → 1 ≤ k → k + ci e v b ≤ S := by
    rintro b k ⟨s', hs', hr'⟩ hk
    obtain ⟨h1, h2, -⟩ := hchk b
    have heq : (fun x => T e.tt (upd x v b)) = T (ri e v b) := funext (rok_sound _ _ _ _ h1)
    rw [heq] at hr'
    have := ih s' (by omega) _ hr'
    omega
  have hNC : ∀ b, Cst (fun x => T e.tt (upd x v b)) → ni e v b = false := by
    intro b hc
    obtain ⟨h1, -, h3⟩ := hchk b
    rw [h3]
    by_contra hn
    simp only [Bool.not_eq_false] at hn
    unfold ncB at hn
    obtain ⟨k, hk, hk'⟩ := rngAny hn
    have := hc (pt k) (pt 0)
    simp only [rok_sound _ _ _ _ h1, T_pt _ _ hk, T_pt _ 0 (by norm_num)] at this
    simp [this] at hk'
  obtain ⟨hr1, hall, hbv, h2⟩ := hF
  have c0 := hCB false r (hall false) hr1
  have c1 := hCB true r (hall true) hr1
  have cb := hCB bv (r + 1) hbv (by omega)
  have co := hCB (!bv) r (hall _) hr1
  rcases Nat.lt_or_ge r 3 with hr3 | hr3
  · rcases Nat.lt_or_ge r 2 with hr2 | hr2
    · refine ⟨0, by norm_num, fun _ => by omega, ?_⟩
      simp only [fact]
      omega
    · obtain ⟨c, hne, heq⟩ := h2 (by omega)
      by_cases hc : c = bv
      · refine ⟨2, by norm_num, by omega, ?_⟩
        simp only [fact]
        rcases heq hc with hh | ⟨hcst, hh⟩
        · have := hCB bv 4 hh (by omega)
          split_ifs <;> omega
        · have := hCB bv 3 hh (by omega)
          simp only [hNC bv hcst, Bool.false_eq_true, if_false]
          omega
      · have hcb : c = !bv := by revert hc; cases c <;> cases bv <;> decide
        subst hcb
        refine ⟨1, by norm_num, by omega, ?_⟩
        simp only [fact]
        rcases hne hc with hh | ⟨hcst, hh⟩
        · have := hCB (!bv) 3 hh (by omega)
          split_ifs <;> omega
        · have := hCB (!bv) 2 hh (by omega)
          simp only [hNC _ hcst, Bool.false_eq_true, if_false]
          omega
  · refine ⟨3, by norm_num, by omega, ?_⟩
    simp only [fact]
    omega

/-- **Soundness.** If the certificate checks, every stored bound is a lower bound on the AIG size. -/
theorem sound (L : List E) (hL : checkAll L = true) : ∀ s tt, Realizes 6 (T tt) s → look L tt ≤ s := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
  intro tt hR
  unfold look
  cases hf : L.find? (fun e => e.tt == tt) with
  | none => simp
  | some e =>
  simp only [Option.map, Option.getD]
  have he : e ∈ L := List.mem_of_find?_eq_some hf
  have htt : e.tt = tt := by simpa using List.find?_some hf
  subst htt
  have hok : okE L e = true := List.all_eq_true.1 hL e he
  obtain ⟨C, hC, hCs⟩ := exists_lexmin hR
  simp only [okE, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at hok
  rcases hok with h0 | ⟨hlit, hrest⟩
  · omega
  obtain ⟨nc, nl⟩ := notLit_sound _ hlit
  have h1size : 1 ≤ C.rgates.length := by
    by_contra hz
    rcases small hC.1 (by omega) with ⟨c, hc⟩ | ⟨u, hu, neg, hc⟩ | ⟨hl1, -⟩
    · exact nc c hc
    · exact nl u hu neg hc
    · omega
  have hsz : C.size = C.rgates.length := rfl
  rcases hrest with h1 | ⟨⟨hgate, hR'⟩, hpairs⟩
  · omega
  have h2size : 2 ≤ C.rgates.length := by
    by_contra hz
    rcases small hC.1 (by omega) with ⟨c, hc⟩ | ⟨u, hu, neg, hc⟩ | ⟨-, i, j, ai, aj, neg, hij, hi, hj, hc⟩
    · exact nc c hc
    · exact nl u hu neg hc
    · exact notGate_sound _ hgate i j hij hi hj ai aj neg hc
  obtain ⟨i, j, ai, aj, hij, hi, hj, hFi, hFj, hfac⟩ := first_gate hC h2size
  obtain ⟨a, ha, ha0, hai⟩ := fact_le L e hR' C.size s hCs ih i hi ai _ hFi
  obtain ⟨b, hb, hb0, hbj⟩ := fact_le L e hR' C.size s hCs ih j hj aj _ hFj
  have hp := rng (rng hpairs i hi) j hj
  simp only [Bool.or_eq_true, beq_iff_eq] at hp
  rcases hp with hp | hp
  · exact absurd hp hij
  have hp' := bools (bools hp ai) aj
  simp only [okPair, Bool.or_eq_true, decide_eq_true_eq] at hp'
  rcases hp' with hp' | hp'
  · have := pairB_le e i j ai aj true a b ha hb (fun _ _ => rfl)
    omega
  · have := pairB_le e i j ai aj (factB e.tt i j ai aj) a b ha hb
      (fun h1 h2 => factB_of _ i j ai aj hij (hfac (ha0 h1) (hb0 h2)))
    omega

/-! ## The posted function -/

theorem checkAll_entries : checkAll entries = true := by decide +kernel

theorem look_root : look entries T16102 = 8 := by decide +kernel

theorem fb_eq : ∀ b0 b1 b2 b3 b4 b5 : Bool,
    Meta16102.fb b0 b1 b2 b3 b4 b5 = T16102.testBit (idxB b0 b1 b2 b3 b4 b5) := by
  decide +kernel

theorem F_eq : Meta16102.F = T T16102 := funext fun x => by
  rw [Meta16102.F, Meta16102.f16102_eq]
  exact fb_eq (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

/-- **Gap (A) closed: the posted function has no free-NOT AIG with 7 gates.** -/
theorem hA : ¬ Realizes 6 Meta16102.F 7 := by
  rw [F_eq]
  intro h
  have := sound entries checkAll_entries 7 _ h
  rw [look_root] at this
  omega

end SatBridge.Meta16102Aig

namespace SatBridge.Meta16102

open PEqualNP.CircuitLowerBounds

/-- `posted_core` with gap (A) discharged: every posted candidate with at most nine gates and a NOT on a
gate wire has exactly eight binary AND/OR gates and one NOT. -/
theorem posted_core_closed (C : Circuit)
    (hfan : PEqualNP.MetaComplexity.FanInTwo C) (hsize : C.size ≤ 9)
    (heval : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = f16102 x)
    (hnot : ∃ g ∈ C.gates, g.op = GateOp.not ∧ 6 ≤ g.inputs.headD 0) :
    C.size = 9 ∧ C.gates.countP isBin = 8 ∧ C.gates.countP (fun g => isNot g.op) = 1 ∧
      (∀ g ∈ C.gates, AndOrNot g.op) :=
  posted_core Meta16102Aig.hA C hfan hsize heval hnot

end SatBridge.Meta16102
