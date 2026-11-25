/-
Exact functional-module contraction (formalized 2026-11-24).

Main result `module_contraction`: if `f(x) = g(h(x_i, x_j), rest)` where `h` is AND or OR and `f`
depends on `x_j`, then `minSize f = minSize g + 1`, in the counted-NOT basis (AND/OR/NOT, every gate
counts) and in the monotone basis (AND/OR).

* Semantics: `wval` evaluates wires by recursion on the wire index (a read of a later wire gives
  `false`, which never happens in a well-formed circuit). A circuit computes `f` if some wire does.
* `run` is one constant-propagation / input-substitution pass. Inputs are bound to constants or new
  wires; a gate with a constant argument, or a binary gate whose arguments became one wire, is dropped
  and its readers are redirected. `pass_circuit` proves it preserves the computed function, the basis
  and well-formedness, never adds gates, and drops the first gate reading an input fixed to a constant.
* Substitution (`substitution`): prepend the module gate and bind g's module input to it.
* Restriction (`restriction`): fix `x_j` to the neutral constant of `h`; some gate reads `x_j` (f
  depends on it), so at least one gate is dropped; `x_i` then plays the module output.
* `minSize_perm`: the position convention for the module input of `g` is without loss of generality.
* `peel_contraction`: the same for the raw peeling step `f = h(x_i, g(rest))`, `g` nonconstant.
* `restrict_const`: single-input gate elimination used by both restriction directions.

These are statements about the mathematical model, not about the Python implementation.
-/
import CircuitLemmas.Basic

set_option linter.deprecated false

namespace CircuitLemmas

/-! ## Evaluation semantics -/

namespace Op

def eval : Op → Bool → Bool → Bool
  | .and, a, b => a && b
  | .or, a, b => a || b
  | .not, a, _ => !a

/-- Neutral constant of a binary gate: `true` for AND, `false` for OR. -/
def neutral : Op → Bool
  | .and => true
  | _ => false

lemma eval_comm {op : Op} (h : op ≠ .not) (a b : Bool) : op.eval a b = op.eval b a := by
  cases op <;> simp_all [eval, Bool.and_comm, Bool.or_comm]

lemma eval_neutral {op : Op} (h : op ≠ .not) (a : Bool) : op.eval a op.neutral = a := by
  cases op <;> simp_all [eval, neutral]

lemma eval_congr {op : Op} {a a' b b' : Bool} (ha : a = a') (hb : op ≠ .not → b = b') :
    op.eval a b = op.eval a' b' := by
  cases op <;> simp_all [eval]

end Op

def Gate.dflt : Gate := ⟨Op.not, 0, 0⟩

/-- Well-formedness of gate `k` (wire `n + k`). `Circuit.WellFormed` is this for every gate. -/
def gateWF (n k : ℕ) (g : Gate) : Prop :=
  (g.op = Op.not → g.l < n + k) ∧ (g.op ≠ Op.not → g.l < g.r ∧ g.r < n + k)

set_option linter.unusedVariables false in
/-- Value of wire `w` when gate `k` is `G k` (wire `n + k`). A read of a wire `≥ w` gives `false`;
under well-formedness that never happens. -/
def wval (n : ℕ) (G : ℕ → Gate) (x : Fin n → Bool) (w : ℕ) : Bool :=
  if h : w < n then x ⟨w, h⟩ else
    (G (w - n)).op.eval
      (if h1 : (G (w - n)).l < w then wval n G x (G (w - n)).l else false)
      (if h2 : (G (w - n)).r < w then wval n G x (G (w - n)).r else false)
termination_by w

lemma wval_eq (n : ℕ) (G : ℕ → Gate) (x : Fin n → Bool) (w : ℕ) :
    wval n G x w = if h : w < n then x ⟨w, h⟩ else
    (G (w - n)).op.eval
      (if (G (w - n)).l < w then wval n G x (G (w - n)).l else false)
      (if (G (w - n)).r < w then wval n G x (G (w - n)).r else false) := by
  rw [wval]; simp only [dite_eq_ite]

lemma wval_input (n : ℕ) (G : ℕ → Gate) (x : Fin n → Bool) (k : Fin n) : wval n G x k = x k := by
  rw [wval_eq, dif_pos k.2]

lemma wval_gate (n : ℕ) (G : ℕ → Gate) (x : Fin n → Bool) (t : ℕ) (hg : gateWF n t (G t)) :
    wval n G x (n + t) = (G t).op.eval (wval n G x (G t).l) (wval n G x (G t).r) := by
  rw [wval_eq, dif_neg (by omega), show n + t - n = t by omega]
  by_cases hop : (G t).op = Op.not
  · have h1 := hg.1 hop
    rw [if_pos h1]
    exact Op.eval_congr rfl (fun h => absurd hop h)
  · obtain ⟨h1, h2⟩ := hg.2 hop
    rw [if_pos (by omega), if_pos h2]

/-- Prefix lemma: wire values depend only on the gates before the wire. -/
lemma wval_congr {n K : ℕ} {G G' : ℕ → Gate} (hG : ∀ k < K, G k = G' k) (x : Fin n → Bool) :
    ∀ w < n + K, wval n G x w = wval n G' x w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    rw [wval_eq n G x w, wval_eq n G' x w]
    by_cases h : w < n
    · rw [dif_pos h, dif_pos h]
    · rw [dif_neg h, dif_neg h, hG (w - n) (by omega)]
      congr 1
      · split_ifs with h1
        · exact ih _ h1 (by omega)
        · rfl
      · split_ifs with h1
        · exact ih _ h1 (by omega)
        · rfl

/-- If no gate reads input `j`, no other wire depends on `x j`. -/
lemma wval_indep {n m : ℕ} {G : ℕ → Gate} (j : Fin n) (hG : ∀ t < m, j.1 ∉ (G t).reads)
    (x : Fin n → Bool) (b : Bool) :
    ∀ w < n + m, w ≠ j.1 → wval n G x w = wval n G (Function.update x j b) w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hne
    rw [wval_eq n G x w, wval_eq n G _ w]
    by_cases h : w < n
    · rw [dif_pos h, dif_pos h, Function.update_of_ne]
      intro e; apply hne; rw [← e]
    · rw [dif_neg h, dif_neg h]
      have hr := hG (w - n) (by omega)
      have key : ∀ v ∈ (G (w - n)).reads,
          (if v < w then wval n G x v else false)
            = (if v < w then wval n G (Function.update x j b) v else false) := by
        intro v hv
        split_ifs with h1
        · exact ih v h1 (by omega) (fun e => hr (e ▸ hv))
        · rfl
      apply Op.eval_congr
      · apply key
        unfold Gate.reads; split_ifs <;> simp
      · intro hop
        apply key
        unfold Gate.reads; rw [if_neg hop]; simp

namespace Circuit

variable {n m : ℕ}

/-- Gate function of a circuit (padded with a dummy gate). -/
def G (c : Circuit n m) (k : ℕ) : Gate := if h : k < m then c.gate ⟨k, h⟩ else Gate.dflt

/-- Value of wire `w` of circuit `c` on input `x`. -/
def eval (c : Circuit n m) (x : Fin n → Bool) (w : ℕ) : Bool := wval n c.G x w

/-- Circuit from a list of gates. -/
def ofList (gs : List Gate) : Circuit n gs.length := ⟨fun k => gs[k.1]'k.2⟩

end Circuit

def listG (gs : List Gate) (k : ℕ) : Gate := if h : k < gs.length then gs[k] else Gate.dflt

lemma ofList_G (gs : List Gate) : (Circuit.ofList (n := n) gs).G = listG gs := rfl

lemma listG_append (gs : List Gate) (g : Gate) : ∀ k < gs.length, listG gs k = listG (gs ++ [g]) k := by
  intro k hk
  unfold listG
  rw [dif_pos hk, dif_pos (by simp; omega), List.getElem_append_left]

lemma listG_last (gs : List Gate) (g : Gate) : listG (gs ++ [g]) gs.length = g := by
  unfold listG; simp

/-- Well-formedness of a gate list over `n` inputs. -/
def WFList (n : ℕ) (gs : List Gate) : Prop := ∀ k (h : k < gs.length), gateWF n k gs[k]

lemma wellFormed_ofList {n : ℕ} {gs : List Gate} (h : WFList n gs) :
    (Circuit.ofList (n := n) gs).WellFormed := fun j => h j.1 j.2

lemma Circuit.gateWF_G {n m : ℕ} (c : Circuit n m) (hw : c.WellFormed) {t : ℕ} (ht : t < m) :
    gateWF n t (c.G t) := by
  unfold Circuit.G; rw [dif_pos ht]; exact hw ⟨t, ht⟩

/-! ## Bases and realizability -/

inductive Basis
  | counted   -- AND, OR, NOT; every gate (including NOT) counts
  | monotone  -- AND, OR only

def Basis.allows : Basis → Op → Prop
  | .counted, _ => True
  | .monotone, op => op ≠ Op.not

def Circuit.InBasis {n m : ℕ} (c : Circuit n m) (b : Basis) : Prop := ∀ j, b.allows (c.gate j).op

/-- Some wire of `c` computes `f`. -/
def Circuit.Computes {n m : ℕ} (c : Circuit n m) (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ o < n + m, ∀ x, c.eval x o = f x

/-- `f` has a well-formed circuit in basis `b` with at most `k` gates. -/
def SizeLE (b : Basis) {n : ℕ} (f : (Fin n → Bool) → Bool) (k : ℕ) : Prop :=
  ∃ m ≤ k, ∃ c : Circuit n m, c.WellFormed ∧ c.InBasis b ∧ c.Computes f

/-- Minimum circuit size (`0` if `f` is not computable in the basis). -/
noncomputable def minSize (b : Basis) {n : ℕ} (f : (Fin n → Bool) → Bool) : ℕ :=
  sInf {k | SizeLE b f k}

/-! ## Constant propagation and input substitution

`run` copies the gates of an old circuit (`n` inputs, gate function `G`) onto a new gate list over `n'`
inputs that starts with `base`. Each old input `k` is bound to a descriptor `init k`: a constant or a
wire of the new circuit. Each old wire gets a descriptor. A gate with a constant argument, or a binary
gate whose two arguments became the same wire, is not copied. -/

inductive Desc
  | const (b : Bool)
  | wire (v : ℕ)

namespace Desc

def val (V : ℕ → Bool) : Desc → Bool
  | .const b => b
  | .wire v => V v

def Valid (B : ℕ) : Desc → Prop
  | .const _ => True
  | .wire v => v < B

lemma Valid.mono {B B' : ℕ} {d : Desc} (h : d.Valid B) (hB : B ≤ B') : d.Valid B' := by
  cases d <;> simp_all [Valid]; omega

lemma val_congr {B : ℕ} {d : Desc} (h : d.Valid B) {V V' : ℕ → Bool} (hV : ∀ v < B, V v = V' v) :
    d.val V = d.val V' := by
  cases d <;> simp_all [val, Valid]

end Desc

/-- Simplify a gate whose arguments have descriptors `a`, `b`: either the result's descriptor
(gate dropped) or the gate to emit. -/
def simpGate (op : Op) (a b : Desc) : Desc ⊕ Gate :=
  match op, a, b with
  | .not, .const v, _ => .inl (.const (!v))
  | .not, .wire w, _ => .inr ⟨.not, w, w⟩
  | op, .const v, b => if v = op.neutral then .inl b else .inl (.const v)
  | op, .wire w, .const v => if v = op.neutral then .inl (.wire w) else .inl (.const v)
  | op, .wire w1, .wire w2 => if w1 = w2 then .inl (.wire w1) else .inr ⟨op, min w1 w2, max w1 w2⟩

lemma simpGate_inl {op : Op} {a b e : Desc} (h : simpGate op a b = .inl e) (V : ℕ → Bool) :
    e.val V = op.eval (a.val V) (b.val V) := by
  cases op <;> cases a <;> cases b <;> simp only [simpGate] at h <;>
    (try split_ifs at h) <;> (try simp only [Sum.inl.injEq] at h) <;> (try subst h) <;> simp_all [Desc.val, Op.eval, Op.neutral]

lemma simpGate_inl_valid {op : Op} {a b e : Desc} {B : ℕ} (h : simpGate op a b = .inl e)
    (ha : a.Valid B) (hb : op ≠ .not → b.Valid B) : e.Valid B := by
  cases op <;> cases a <;> cases b <;> simp only [simpGate] at h <;>
    (try split_ifs at h) <;> (try simp only [Sum.inl.injEq] at h) <;> (try subst h) <;> simp_all [Desc.Valid]

lemma simpGate_inr {op : Op} {a b : Desc} {g : Gate} (h : simpGate op a b = .inr g) :
    (op = .not ∧ ∃ w, a = .wire w ∧ g = ⟨.not, w, w⟩) ∨
    (op ≠ .not ∧ ∃ w1 w2, a = .wire w1 ∧ b = .wire w2 ∧ w1 ≠ w2 ∧ g = ⟨op, min w1 w2, max w1 w2⟩) := by
  cases op <;> cases a <;> cases b <;> simp only [simpGate] at h <;>
    (try split_ifs at h) <;> simp_all

/-- A gate reading a wire with a constant descriptor is dropped. -/
lemma simpGate_of_reads_const {g : Gate} {d : ℕ → Desc} {w : ℕ} {v : Bool} (hw : w ∈ g.reads)
    (hd : d w = .const v) : ∃ e, simpGate g.op (d g.l) (d g.r) = .inl e := by
  unfold Gate.reads at hw
  split_ifs at hw with hop
  · rw [Finset.mem_singleton] at hw; subst hw; rw [hop, hd]; exact ⟨_, rfl⟩
  · rw [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · rw [hd]; cases h : g.op <;> simp_all [simpGate] <;> split_ifs <;> simp
    · rw [hd]; cases h : g.op <;> cases d g.l <;> simp_all [simpGate] <;> split_ifs <;> simp

structure St where
  gs : List Gate
  d : ℕ → Desc

def St.step (n n' : ℕ) (s : St) (t : ℕ) (g : Gate) : St :=
  match simpGate g.op (s.d g.l) (s.d g.r) with
  | .inl e => ⟨s.gs, Function.update s.d (n + t) e⟩
  | .inr g' => ⟨s.gs ++ [g'], Function.update s.d (n + t) (.wire (n' + s.gs.length))⟩

def run (n n' : ℕ) (base : List Gate) (init : Fin n → Desc) (G : ℕ → Gate) : ℕ → St
  | 0 => ⟨base, fun w => if h : w < n then init ⟨w, h⟩ else .const false⟩
  | t + 1 => (run n n' base init G t).step n n' t (G t)

lemma step_len (n n' : ℕ) (s : St) (t : ℕ) (g : Gate) :
    (s.step n n' t g).gs.length ≤ s.gs.length + 1 := by
  unfold St.step; split <;> simp

lemma run_len_mono (n n' : ℕ) (base : List Gate) (init : Fin n → Desc) (G : ℕ → Gate) (t1 : ℕ) :
    ∀ t2, t1 ≤ t2 →
      (run n n' base init G t2).gs.length ≤ (run n n' base init G t1).gs.length + (t2 - t1) := by
  intro t2 h
  induction t2 with
  | zero => simp_all
  | succ t ih =>
    rcases Nat.eq_or_lt_of_le h with e | lt
    · rw [e]; simp
    · have := ih (by omega)
      have := step_len n n' (run n n' base init G t) t (G t)
      simp only [run]; omega

lemma run_inputs (n n' : ℕ) (base : List Gate) (init : Fin n → Desc) (G : ℕ → Gate) :
    ∀ t, ∀ k : Fin n, (run n n' base init G t).d k = init k := by
  intro t k
  induction t with
  | zero => simp [run]
  | succ t ih =>
    simp only [run, St.step]
    split <;> (dsimp only; rw [Function.update_of_ne (by omega)]; exact ih)

/-- Main invariant of the pass after `t` old gates. -/
structure PassInv (n n' : ℕ) (b : Basis) (G : ℕ → Gate) (base : List Gate) (init : Fin n → Desc)
    (t : ℕ) (s : St) : Prop where
  prefix_ : base <+: s.gs
  wf : WFList n' s.gs
  basis : ∀ g ∈ s.gs, b.allows g.op
  len : s.gs.length ≤ base.length + t
  valid : ∀ w < n + t, (s.d w).Valid (n' + s.gs.length)
  sem : ∀ y : Fin n' → Bool, ∀ w < n + t, (s.d w).val (wval n' (listG s.gs) y)
    = wval n G (fun k => (init k).val (wval n' (listG base) y)) w

lemma prefix_vals {n' : ℕ} {base gs : List Gate} (hp : base <+: gs) (y : Fin n' → Bool) :
    ∀ v < n' + base.length, wval n' (listG gs) y v = wval n' (listG base) y v := by
  apply wval_congr
  intro k hk
  obtain ⟨r, rfl⟩ := hp
  unfold listG; rw [dif_pos (by simp; omega), dif_pos hk, List.getElem_append_left]

theorem pass_inv {n n' m : ℕ} {b : Basis} {G : ℕ → Gate} {base : List Gate} {init : Fin n → Desc}
    (hG : ∀ t < m, gateWF n t (G t)) (hGb : ∀ t < m, b.allows (G t).op)
    (hbase : WFList n' base) (hbaseb : ∀ g ∈ base, b.allows g.op)
    (hinit : ∀ k, (init k).Valid (n' + base.length)) :
    ∀ t ≤ m, PassInv n n' b G base init t (run n n' base init G t) := by
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨List.prefix_refl _, hbase, hbaseb, by simp [run], ?_, ?_⟩
    · intro w hw; simp only [run]; rw [dif_pos (by omega)]; exact hinit _
    · intro y w hw
      simp only [run]; rw [dif_pos (by omega), wval_eq n G _ w, dif_pos (show w < n by omega)]
  | succ t ih =>
    intro ht
    have I := ih (by omega)
    set s := run n n' base init G t with hs
    have hgt := hG t (by omega)
    set g := G t with hg
    -- descriptors of the arguments
    have hla : (s.d g.l).Valid (n' + s.gs.length) := by
      apply I.valid; by_cases hop : g.op = Op.not
      · exact hgt.1 hop
      · have := hgt.2 hop; omega
    have hlb : g.op ≠ Op.not → (s.d g.r).Valid (n' + s.gs.length) := fun hop =>
      I.valid _ (hgt.2 hop).2
    have hsa : ∀ y, (s.d g.l).val (wval n' (listG s.gs) y)
        = wval n G (fun k => (init k).val (wval n' (listG base) y)) g.l := by
      intro y; apply I.sem; by_cases hop : g.op = Op.not
      · exact hgt.1 hop
      · have := hgt.2 hop; omega
    have hsb : ∀ y, g.op ≠ Op.not → (s.d g.r).val (wval n' (listG s.gs) y)
        = wval n G (fun k => (init k).val (wval n' (listG base) y)) g.r := fun y hop =>
      I.sem y _ (hgt.2 hop).2
    have hold : ∀ y, wval n G (fun k => (init k).val (wval n' (listG base) y)) (n + t)
        = g.op.eval ((s.d g.l).val (wval n' (listG s.gs) y))
            ((s.d g.r).val (wval n' (listG s.gs) y)) := by
      intro y; rw [wval_gate n G _ t hgt]
      exact Op.eval_congr (hsa y).symm (fun hop => (hsb y hop).symm)
    simp only [run]
    rw [← hs]
    unfold St.step
    rw [← hg]
    split
    · rename_i e he
      refine ⟨I.prefix_, I.wf, I.basis, by dsimp only; have := I.len; omega, ?_, ?_⟩
      · intro w hw
        by_cases hw' : w = n + t
        · subst hw'; dsimp only; rw [Function.update_self]; exact simpGate_inl_valid he hla hlb
        · dsimp only; rw [Function.update_of_ne hw']; exact I.valid w (by omega)
      · intro y w hw
        by_cases hw' : w = n + t
        · subst hw'; dsimp only; rw [Function.update_self, simpGate_inl he, hold]
        · dsimp only; rw [Function.update_of_ne hw']; exact I.sem y w (by omega)
    · rename_i g' he
      have hlen := I.len
      have hpre : ∀ y, ∀ v < n' + s.gs.length,
          wval n' (listG (s.gs ++ [g'])) y v = wval n' (listG s.gs) y v := fun y =>
        wval_congr (fun k hk => (listG_append s.gs g' k hk).symm) y
      have hshape := simpGate_inr he
      have hg'op : g'.op = g.op := by
        rcases hshape with ⟨hop, w, ha, rfl⟩ | ⟨hop, w1, w2, ha, hb, hne, rfl⟩
        · exact hop.symm
        · rfl
      have hg'wf : gateWF n' s.gs.length g' := by
        rcases hshape with ⟨hop, w, ha, rfl⟩ | ⟨hop, w1, w2, ha, hb, hne, rfl⟩
        · rw [ha] at hla; simp only [Desc.Valid] at hla
          exact ⟨fun _ => hla, fun h => absurd rfl h⟩
        · have hlb' := hlb hop
          rw [ha] at hla; rw [hb] at hlb'; simp only [Desc.Valid] at hla hlb'
          refine ⟨fun h => absurd h hop, fun _ => ⟨?_, ?_⟩⟩ <;> dsimp only <;> omega
      have hnew : ∀ y, wval n' (listG (s.gs ++ [g'])) y (n' + s.gs.length)
          = g.op.eval ((s.d g.l).val (wval n' (listG s.gs) y))
              ((s.d g.r).val (wval n' (listG s.gs) y)) := by
        intro y
        have hwf' : gateWF n' s.gs.length (listG (s.gs ++ [g']) s.gs.length) := by
          rw [listG_last]; exact hg'wf
        rw [wval_gate _ _ _ _ hwf', listG_last]
        rcases hshape with ⟨hop, w, ha, rfl⟩ | ⟨hop, w1, w2, ha, hb, hne, rfl⟩
        · rw [ha] at hla ⊢; simp only [Desc.Valid] at hla
          simp only [Desc.val, hop, Op.eval]; rw [hpre y w hla]
        · have hlb' := hlb hop
          rw [ha] at hla ⊢; rw [hb] at hlb' ⊢; simp only [Desc.Valid] at hla hlb'
          simp only [Desc.val]
          rw [hpre y _ (by omega), hpre y _ (by omega)]
          rcases le_total w1 w2 with h | h
          · rw [min_eq_left h, max_eq_right h]
          · rw [min_eq_right h, max_eq_left h, Op.eval_comm hop]
      refine ⟨I.prefix_.trans (List.prefix_append _ _), ?_, ?_, ?_, ?_, ?_⟩
      · intro k hk
        dsimp only at hk ⊢
        rcases Nat.lt_or_ge k s.gs.length with h | h
        · rw [List.getElem_append_left h]; exact I.wf k h
        · have hk' : k = s.gs.length := by simp at hk; omega
          subst hk'; simpa using hg'wf
      · intro x hx; dsimp only at hx; rw [List.mem_append] at hx; rcases hx with hx | hx
        · exact I.basis x hx
        · simp only [List.mem_singleton] at hx; subst hx; rw [hg'op]; exact hGb t (by omega)
      · dsimp only; simp; omega
      · intro w hw; dsimp only
        by_cases hw' : w = n + t
        · subst hw'; rw [Function.update_self]; simp [Desc.Valid]
        · rw [Function.update_of_ne hw']; exact (I.valid w (by omega)).mono (by simp)
      · intro y w hw; dsimp only
        by_cases hw' : w = n + t
        · subst hw'; rw [Function.update_self]; exact (hnew y).trans (hold y).symm
        · rw [Function.update_of_ne hw', ← I.sem y w (by omega)]
          exact Desc.val_congr (I.valid w (by omega)) (hpre y)

/-- The first gate reading an input bound to a constant is dropped. -/
lemma run_len_drop {n n' : ℕ} {base : List Gate} {init : Fin n → Desc} {G : ℕ → Gate} {t0 t : ℕ}
    (ht : t0 < t) {j : Fin n} {v : Bool} (hj : init j = .const v) (hr : j.1 ∈ (G t0).reads) :
    (run n n' base init G t).gs.length + 1 ≤ (run n n' base init G t0).gs.length + (t - t0) := by
  have h1 := run_len_mono n n' base init G (t0 + 1) t (by omega)
  have h2 : (run n n' base init G (t0 + 1)).gs.length = (run n n' base init G t0).gs.length := by
    obtain ⟨e, he⟩ := simpGate_of_reads_const (d := (run n n' base init G t0).d) hr
      (by rw [run_inputs]; exact hj)
    simp only [run, St.step, he]
  omega

/-- The pass applied to a circuit: a circuit over `n'` inputs computing `F`, with at most
`base.length + m` gates, one fewer if some gate reads an input bound to a constant. -/
theorem pass_circuit {n n' m : ℕ} {b : Basis} (c : Circuit n m) (hw : c.WellFormed)
    (hb : c.InBasis b) {base : List Gate} (hbase : WFList n' base)
    (hbaseb : ∀ g ∈ base, b.allows g.op) {init : Fin n → Desc}
    (hinit : ∀ k, (init k).Valid (n' + base.length))
    {f : (Fin n → Bool) → Bool} {F : (Fin n' → Bool) → Bool}
    (hF : ∀ y, F y = f (fun k => (init k).val (wval n' (listG base) y)))
    (hc : c.Computes f) (hnc : ∀ v, ¬ ∀ y, F y = v) :
    ∃ m', m' ≤ base.length + m ∧
      (∀ (j : Fin n) (v : Bool), init j = .const v →
        (∃ t, ∃ ht : t < m, j.1 ∈ (c.gate ⟨t, ht⟩).reads) → m' + 1 ≤ base.length + m) ∧
      ∃ c' : Circuit n' m', c'.WellFormed ∧ c'.InBasis b ∧ c'.Computes F := by
  obtain ⟨o, ho, hof⟩ := hc
  have hGb : ∀ t < m, b.allows (c.G t).op := fun t ht => by
    unfold Circuit.G; rw [dif_pos ht]; exact hb _
  have hGw : ∀ t < m, gateWF n t (c.G t) := fun t ht => c.gateWF_G hw ht
  have I := pass_inv hGw hGb hbase hbaseb hinit m le_rfl
  refine ⟨(run n n' base init c.G m).gs.length, I.len, ?_, ?_⟩
  · rintro j v hj ⟨t, ht, hr⟩
    have hd := run_len_drop (n' := n') (base := base) (G := c.G) ht hj
      (by unfold Circuit.G; rw [dif_pos ht]; exact hr)
    have := (pass_inv hGw hGb hbase hbaseb hinit t ht.le).len
    omega
  · have hval := I.valid o ho
    have hsem := fun y => I.sem y o ho
    cases hd : (run n n' base init c.G m).d o with
    | const v =>
      exfalso; apply hnc v; intro y
      rw [hF, ← hof]; unfold Circuit.eval; rw [← hsem y, hd]; rfl
    | wire u =>
      rw [hd] at hval
      refine ⟨Circuit.ofList _, wellFormed_ofList I.wf, fun j => I.basis _ (List.getElem_mem _),
        u, hval, fun y => ?_⟩
      unfold Circuit.eval; rw [ofList_G, hF, ← hof]; unfold Circuit.eval; rw [← hsem y, hd]; rfl

lemma Basis.allows_of_ne {b : Basis} {op : Op} (h : op ≠ Op.not) : b.allows op := by
  cases b <;> simp [Basis.allows, h]

/-! ## Input renaming -/

/-- Substituting inputs (`x_k := y_{σ k}`) never increases size, for a nonconstant result. -/
theorem sizeLE_comp {n n' : ℕ} {b : Basis} {f : (Fin n → Bool) → Bool} (σ : Fin n → Fin n')
    (hnc : ∀ v, ¬ ∀ y : Fin n' → Bool, f (fun k => y (σ k)) = v) {k : ℕ} (h : SizeLE b f k) :
    SizeLE b (fun y => f (fun k => y (σ k))) k := by
  obtain ⟨m, hm, c, hw, hb, hc⟩ := h
  obtain ⟨m', hm', -, c', hc'⟩ := pass_circuit (base := []) (init := fun k => .wire (σ k).1)
    c hw hb (fun k h => by simp at h) (by simp) (fun k => by simp [Desc.Valid])
    (F := fun y => f (fun k => y (σ k))) (fun y => by simp only [Desc.val, wval_input]) hc hnc
  exact ⟨m', by simp at hm'; omega, c', hc'⟩

/-- Minimum size is invariant under permuting the inputs of a nonconstant function. -/
theorem minSize_perm {n n' : ℕ} {b : Basis} {f : (Fin n → Bool) → Bool} (e : Fin n ≃ Fin n')
    (hnc : ∀ v, ¬ ∀ x, f x = v) : minSize b (fun y => f (fun k => y (e k))) = minSize b f := by
  have hnc' : ∀ v, ¬ ∀ y : Fin n' → Bool, f (fun k => y (e k)) = v := by
    intro v hv; apply hnc v; intro x
    have := hv (fun k => x (e.symm k)); simpa using this
  unfold minSize; congr 1; ext k; simp only [Set.mem_setOf_eq]
  constructor
  · intro h
    have h2 := sizeLE_comp (b := b) e.symm (by simpa using hnc) h
    simpa using h2
  · exact sizeLE_comp e hnc'

/-! ## Fixing an input to a constant -/

/-- `f` depends on input `j`. -/
def Essential {N : ℕ} (f : (Fin N → Bool) → Bool) (j : Fin N) : Prop :=
  ∃ x, f x ≠ f (Function.update x j (!x j))

lemma nonconst_of_essential {N : ℕ} {f : (Fin N → Bool) → Bool} {j : Fin N} (h : Essential f j) :
    ∀ v, ¬ ∀ x, f x = v := by
  intro v hv; obtain ⟨x, hx⟩ := h; exact hx (by rw [hv, hv])

/-- Single-input gate elimination: fixing an input `x_j` that `f` depends on to a constant `v`
(with a nonconstant result) yields a circuit with at least one gate fewer. The first gate reading
`x_j` is dropped; constants propagate through the gates. -/
theorem restrict_const {n m : ℕ} {b : Basis} {f : (Fin (n + 1) → Bool) → Bool} (j : Fin (n + 1))
    (v : Bool) (hj : Essential f j) (hnc : ∀ u, ¬ ∀ y, f (Fin.insertNth j v y) = u)
    (c : Circuit (n + 1) m) (hw : c.WellFormed) (hb : c.InBasis b) (hc : c.Computes f) :
    ∃ m', m' + 1 ≤ m ∧ ∃ c' : Circuit n m', c'.WellFormed ∧ c'.InBasis b ∧
      c'.Computes (fun y => f (Fin.insertNth j v y)) := by
  set init : Fin (n + 1) → Desc := Fin.insertNth j (Desc.const v) (fun k => .wire k.1) with hinit
  have hiv : ∀ k, (init k).Valid (n + ([] : List Gate).length) := by
    intro k
    refine Fin.succAboveCases j ?_ (fun k => ?_) k
    · simp [hinit, Desc.Valid]
    · simp [hinit, Desc.Valid]
  have hval : ∀ y : Fin n → Bool,
      (fun w => (init w).val (wval n (listG []) y)) = Fin.insertNth j v y := by
    intro y; funext w
    refine Fin.succAboveCases j ?_ (fun k => ?_) w
    · simp [hinit, Desc.val]
    · simp only [hinit, Fin.insertNth_apply_succAbove, Desc.val]; exact wval_input _ _ _ _
  obtain ⟨m', hm', hdrop, c', hc'⟩ := pass_circuit (base := []) (init := init) c hw hb
    (fun k h => by simp at h) (by simp) hiv (F := fun y => f (Fin.insertNth j v y))
    (fun y => by rw [hval]) hc hnc
  refine ⟨m', ?_, c', hc'⟩
  -- some gate reads x_j
  have hread : ∃ t, ∃ ht : t < m, j.1 ∈ (c.gate ⟨t, ht⟩).reads := by
    by_contra hno
    push Not at hno
    obtain ⟨o, ho, hof⟩ := hc
    by_cases hoj : o = j.1
    · apply hnc v; intro y
      rw [← hof]; unfold Circuit.eval; subst hoj
      rw [wval_input, Fin.insertNth_apply_same]
    · obtain ⟨x, hx⟩ := hj
      apply hx
      rw [← hof, ← hof]; unfold Circuit.eval
      refine wval_indep j (fun t ht => ?_) x _ o ho hoj
      unfold Circuit.G; rw [dif_pos ht]; exact hno t ht
  have := hdrop j v (by simp [hinit]) hread
  simpa using this

/-- From `SizeLE f (k+1) ↔ SizeLE g k` and `¬ SizeLE f 0`: `minSize f = minSize g + 1`. -/
lemma minSize_eq_succ {n n' : ℕ} {b : Basis} {f : (Fin n → Bool) → Bool}
    {g : (Fin n' → Bool) → Bool} (hiff : ∀ k, SizeLE b f (k + 1) ↔ SizeLE b g k)
    (h0 : ¬ SizeLE b f 0) (hfin : ∃ k, SizeLE b g k) : minSize b f = minSize b g + 1 := by
  have hgmem : SizeLE b g (minSize b g) :=
    Nat.sInf_mem (show Set.Nonempty {k | SizeLE b g k} from hfin)
  apply le_antisymm
  · exact Nat.sInf_le ((hiff _).2 hgmem)
  · have hfmem : SizeLE b f (minSize b f) :=
      Nat.sInf_mem (show Set.Nonempty {k | SizeLE b f k} from ⟨_, (hiff _).2 hgmem⟩)
    obtain ⟨k', hk'⟩ : ∃ k', minSize b f = k' + 1 :=
      Nat.exists_eq_succ_of_ne_zero (fun h => h0 (h ▸ hfmem))
    rw [hk'] at hfmem ⊢
    have : minSize b g ≤ k' := Nat.sInf_le ((hiff k').1 hfmem)
    omega

/-! ## The module-contraction theorem

`f` has `n + 1` inputs, `g` has `n`. The module reads `x_i` and `x_j` with `i = j.succAbove i'`; `g`
receives the module output at position `i'` and the other inputs of `f` in order (input `j` deleted).
Any two distinct positions `i ≠ j` arise this way. -/

section Module

variable {n : ℕ} {b : Basis} {op : Op} (hop : op ≠ Op.not) (j : Fin (n + 1)) (i' : Fin n)
  {f : (Fin (n + 1) → Bool) → Bool} {g : (Fin n → Bool) → Bool}

/-- `f` is `g` with a raw AND/OR module on inputs `j.succAbove i'` and `j`. -/
def IsModule (op : Op) (j : Fin (n + 1)) (i' : Fin n) (f : (Fin (n + 1) → Bool) → Bool)
    (g : (Fin n → Bool) → Bool) : Prop :=
  ∀ x, f x = g (Function.update (fun k => x (j.succAbove k)) i' (op.eval (x (j.succAbove i')) (x j)))

include hop in
/-- Substitution: a circuit for `g` plus one module gate computes `f`. -/
theorem substitution (hmod : IsModule op j i' f g) (hj : Essential f j) {m : ℕ} (c : Circuit n m)
    (hw : c.WellFormed) (hb : c.InBasis b) (hc : c.Computes g) :
    ∃ m' ≤ m + 1, ∃ c' : Circuit (n + 1) m', c'.WellFormed ∧ c'.InBasis b ∧ c'.Computes f := by
  set i : Fin (n + 1) := j.succAbove i' with hi
  have hne : i.1 ≠ j.1 := fun h => Fin.succAbove_ne j i' (Fin.ext h)
  set base : List Gate := [⟨op, min i.1 j.1, max i.1 j.1⟩] with hbase
  have hbwf : WFList (n + 1) base := by
    intro k hk
    have hk0 : k = 0 := by simp [hbase] at hk; omega
    subst hk0
    refine ⟨fun h => absurd h hop, fun _ => ⟨?_, ?_⟩⟩ <;> simp [hbase] <;> omega
  have hbb : ∀ g ∈ base, b.allows g.op := by
    intro g hg; simp [hbase] at hg; subst hg; exact Basis.allows_of_ne hop
  set init : Fin n → Desc := fun k => if k = i' then .wire (n + 1) else .wire (j.succAbove k).1
    with hinit
  have hiv : ∀ k, (init k).Valid (n + 1 + base.length) := by
    intro k; simp only [hinit, hbase]; split_ifs <;> simp [Desc.Valid]
  have hval : ∀ y : Fin (n + 1) → Bool,
      (fun k => (init k).val (wval (n + 1) (listG base) y))
        = Function.update (fun k => y (j.succAbove k)) i' (op.eval (y i) (y j)) := by
    intro y; funext k
    by_cases hk : k = i'
    · subst hk
      simp only [hinit, if_true, Function.update_self, Desc.val]
      have h0 : gateWF (n + 1) 0 (listG base 0) := hbwf 0 (by simp [hbase])
      have hg0 : wval (n + 1) (listG base) y (n + 1) = (listG base 0).op.eval (wval (n + 1) (listG base) y (listG base 0).l) (wval (n + 1) (listG base) y (listG base 0).r) := wval_gate (n + 1) (listG base) y 0 h0
      rw [hg0]
      have hl : (listG base 0) = ⟨op, min i.1 j.1, max i.1 j.1⟩ := by simp [listG, hbase]
      rw [hl]; dsimp only
      rcases le_total i.1 j.1 with h | h
      · rw [min_eq_left h, max_eq_right h, wval_input _ _ _ i, wval_input _ _ _ j]
      · rw [min_eq_right h, max_eq_left h, wval_input _ _ _ i, wval_input _ _ _ j, Op.eval_comm hop]
    · simp only [hinit, if_neg hk, Function.update_of_ne hk, Desc.val]
      exact wval_input _ _ _ _
  obtain ⟨m', hm', -, c', hc'⟩ := pass_circuit (base := base) (init := init) c hw hb hbwf hbb hiv
    (F := f) (fun y => by rw [hval, hmod y]) hc (nonconst_of_essential hj)
  exact ⟨m', by simpa [hbase, Nat.add_comm] using hm', c', hc'⟩

include hop in
/-- Restriction: fixing `x_j` to the neutral constant of the module removes at least one gate and
leaves a circuit for `g` (input `x_i` plays the module output). -/
theorem restriction (hmod : IsModule op j i' f g) (hj : Essential f j) {m : ℕ}
    (c : Circuit (n + 1) m) (hw : c.WellFormed) (hb : c.InBasis b) (hc : c.Computes f) :
    ∃ m', m' + 1 ≤ m ∧ ∃ c' : Circuit n m', c'.WellFormed ∧ c'.InBasis b ∧ c'.Computes g := by
  have hg : ∀ y, f (Fin.insertNth j op.neutral y) = g y := by
    intro y
    rw [hmod]; congr 1
    simp only [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_same, Op.eval_neutral hop]
    exact Function.update_eq_self i' y
  have hgnc : ∀ v, ¬ ∀ y, f (Fin.insertNth j op.neutral y) = v := by
    intro v hv
    apply nonconst_of_essential hj v
    intro x; rw [hmod x, ← hg]; exact hv _
  obtain ⟨m', hm', c', hw', hb', o, ho, hof⟩ := restrict_const j op.neutral hj hgnc c hw hb hc
  exact ⟨m', hm', c', hw', hb', o, ho, fun y => by rw [hof]; exact hg y⟩

include hop in
theorem module_sizeLE (hmod : IsModule op j i' f g) (hj : Essential f j) (k : ℕ) :
    SizeLE b f (k + 1) ↔ SizeLE b g k := by
  constructor
  · rintro ⟨m, hm, c, hw, hb, hc⟩
    obtain ⟨m', hm', c', hc'⟩ := restriction hop j i' hmod hj c hw hb hc
    exact ⟨m', by omega, c', hc'⟩
  · rintro ⟨m, hm, c, hw, hb, hc⟩
    obtain ⟨m', hm', c', hc'⟩ := substitution hop j i' hmod hj c hw hb hc
    exact ⟨m', by omega, c', hc'⟩

include hop in
theorem module_not_sizeLE_zero (hmod : IsModule op j i' f g) (hj : Essential f j) :
    ¬ SizeLE b f 0 := by
  rintro ⟨m, hm, c, hw, hb, hc⟩
  obtain ⟨m', hm', -⟩ := restriction hop j i' hmod hj c hw hb hc
  omega

include hop in
/-- **Exact module contraction.** If `f = g(h(x_i, x_j), rest)` for a raw AND/OR module `h` and `f`
depends on `x_j`, then `min(f) = min(g) + 1`, in the counted-NOT basis and in the monotone basis
(`hfin`: `g` is computable in the basis; automatic for the counted basis). -/
theorem module_contraction (hmod : IsModule op j i' f g) (hj : Essential f j)
    (hfin : ∃ k, SizeLE b g k) : minSize b f = minSize b g + 1 :=
  minSize_eq_succ (module_sizeLE hop j i' hmod hj) (module_not_sizeLE_zero hop j i' hmod hj) hfin

end Module

/-! ## Peeling a canalizing input

`f(x) = h(x_i, g(rest))` with `h` AND or OR and `g` nonconstant (the raw `peel` step of
`theory/module_contraction.py`). -/

lemma Op.eval_absorb {op : Op} (h : op ≠ .not) (a : Bool) : op.eval (!op.neutral) a = !op.neutral := by
  cases op <;> simp_all [Op.eval, Op.neutral]

lemma Op.eval_neutral_left {op : Op} (h : op ≠ .not) (a : Bool) : op.eval op.neutral a = a := by
  rw [Op.eval_comm h, Op.eval_neutral h]

section Peel

variable {n : ℕ} {b : Basis} {op : Op} (hop : op ≠ Op.not) (i : Fin (n + 1))
  {f : (Fin (n + 1) → Bool) → Bool} {g : (Fin n → Bool) → Bool}

/-- `f = h(x_i, g(other inputs))`. -/
def IsPeel (op : Op) (i : Fin (n + 1)) (f : (Fin (n + 1) → Bool) → Bool)
    (g : (Fin n → Bool) → Bool) : Prop :=
  ∀ x, f x = op.eval (x i) (g (fun k => x (i.succAbove k)))

include hop in
theorem peel_restriction (hpeel : IsPeel op i f g) (hg : ∀ v, ¬ ∀ y, g y = v) {m : ℕ}
    (c : Circuit (n + 1) m) (hw : c.WellFormed) (hb : c.InBasis b) (hc : c.Computes f) :
    ∃ m', m' + 1 ≤ m ∧ ∃ c' : Circuit n m', c'.WellFormed ∧ c'.InBasis b ∧ c'.Computes g := by
  have hfi : ∀ y, f (Fin.insertNth i op.neutral y) = g y := by
    intro y; rw [hpeel]
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, Op.eval_neutral_left hop]
  have hess : Essential f i := by
    obtain ⟨y, hy⟩ : ∃ y, g y ≠ !op.neutral := by
      by_contra h; push Not at h; exact hg _ h
    refine ⟨Fin.insertNth i op.neutral y, fun heq => hy ?_⟩
    rw [← hfi y, heq, hpeel]
    simp only [Function.update_self, Fin.insertNth_apply_same]
    exact Op.eval_absorb hop _
  obtain ⟨m', hm', c', hw', hb', o, ho, hof⟩ := restrict_const i op.neutral hess
    (fun u hu => hg u (fun y => by rw [← hfi]; exact hu y)) c hw hb hc
  exact ⟨m', hm', c', hw', hb', o, ho, fun y => by rw [hof]; exact hfi y⟩

include hop in
theorem peel_substitution (hpeel : IsPeel op i f g) (hg : ∀ v, ¬ ∀ y, g y = v) {m : ℕ}
    (c : Circuit n m) (hw : c.WellFormed) (hb : c.InBasis b) (hc : c.Computes g) :
    ∃ m' ≤ m + 1, ∃ c' : Circuit (n + 1) m', c'.WellFormed ∧ c'.InBasis b ∧ c'.Computes f := by
  set G : (Fin (n + 1) → Bool) → Bool := fun y => g (fun k => y (i.succAbove k)) with hG
  have hGnc : ∀ v, ¬ ∀ y, G y = v := by
    intro v hv; apply hg v; intro y'
    have := hv (Fin.insertNth i false y')
    simpa [hG, Fin.insertNth_apply_succAbove] using this
  -- copy the circuit for g onto the inputs other than x_i
  obtain ⟨m1, hm1, -, c1, hw1, hb1, u, hu, hu1⟩ := pass_circuit (base := [])
    (init := fun k => .wire (i.succAbove k).1) c hw hb (fun k h => by simp at h) (by simp)
    (fun k => by have := (i.succAbove k).2; simp only [Desc.Valid, List.length_nil]; omega) (F := G) (fun y => by simp only [hG, Desc.val, wval_input]) hc hGnc
  have hui : u ≠ i.1 := by
    intro e; subst e
    have h0 := hu1 (Fin.insertNth i false (fun _ => false))
    have h1 := hu1 (Fin.insertNth i true (fun _ => false))
    unfold Circuit.eval at h0 h1
    rw [wval_input, Fin.insertNth_apply_same] at h0 h1
    simp only [hG, Fin.insertNth_apply_succAbove] at h0 h1
    rw [← h0] at h1; exact Bool.noConfusion h1
  -- append the gate h(x_i, out)
  set gs1 := List.ofFn c1.gate with hgs1
  have hlen1 : gs1.length = m1 := by simp [hgs1]
  have hG1 : listG gs1 = c1.G := by
    funext k; unfold listG Circuit.G
    by_cases hk : k < m1
    · rw [dif_pos (by omega), dif_pos hk]; simp [hgs1]
    · rw [dif_neg (by omega), dif_neg hk]
  set ng : Gate := ⟨op, min u i.1, max u i.1⟩ with hng
  have hi := i.2
  refine ⟨(gs1 ++ [ng]).length, by simp only [List.length_append, List.length_singleton, hlen1]; simp at hm1; omega, Circuit.ofList (gs1 ++ [ng]), ?_, ?_, ?_⟩
  · apply wellFormed_ofList
    intro k hk
    rcases Nat.lt_or_ge k gs1.length with h | h
    · rw [List.getElem_append_left h]
      have := hw1 ⟨k, by omega⟩
      simpa [hgs1, gateWF] using this
    · have hk' : k = gs1.length := by simp at hk; omega
      subst hk'
      simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_cons_zero]
      refine ⟨fun h => absurd h hop, fun _ => ⟨?_, ?_⟩⟩ <;> simp only [hng] <;> omega
  · intro k
    show b.allows ((gs1 ++ [ng])[k.1]'k.2).op
    rcases Nat.lt_or_ge k.1 gs1.length with h | h
    · rw [List.getElem_append_left h]
      have := hb1 ⟨k.1, by omega⟩
      simpa [hgs1] using this
    · have hk' : k.1 = gs1.length := by have := k.2; simp at this; omega
      simp only [hk', List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
        List.getElem_cons_zero, hng]
      exact Basis.allows_of_ne hop
  · refine ⟨n + 1 + gs1.length, by simp, fun y => ?_⟩
    unfold Circuit.eval; rw [ofList_G]
    have hwf' : gateWF (n + 1) gs1.length (listG (gs1 ++ [ng]) gs1.length) := by
      rw [listG_last]
      refine ⟨fun h => absurd h hop, fun _ => ⟨?_, ?_⟩⟩ <;> simp only [hng] <;> omega
    rw [wval_gate _ _ _ _ hwf', listG_last]
    have hpre : ∀ v < n + 1 + gs1.length,
        wval (n + 1) (listG (gs1 ++ [ng])) y v = wval (n + 1) (listG gs1) y v :=
      wval_congr (fun k hk => (listG_append gs1 ng k hk).symm) y
    simp only [hng]
    rw [hpre _ (by omega), hpre _ (by omega), hG1, hpeel y]
    have hu' : wval (n + 1) c1.G y u = G y := hu1 y
    have hi' : wval (n + 1) c1.G y i.1 = y i := wval_input _ _ _ i
    rcases le_total u i.1 with h | h
    · rw [min_eq_left h, max_eq_right h, hu', hi', Op.eval_comm hop]
    · rw [min_eq_right h, max_eq_left h, hu', hi']

include hop in
theorem peel_sizeLE (hpeel : IsPeel op i f g) (hg : ∀ v, ¬ ∀ y, g y = v) (k : ℕ) :
    SizeLE b f (k + 1) ↔ SizeLE b g k := by
  constructor
  · rintro ⟨m, hm, c, hw, hb, hc⟩
    obtain ⟨m', hm', c', hc'⟩ := peel_restriction hop i hpeel hg c hw hb hc
    exact ⟨m', by omega, c', hc'⟩
  · rintro ⟨m, hm, c, hw, hb, hc⟩
    obtain ⟨m', hm', c', hc'⟩ := peel_substitution hop i hpeel hg c hw hb hc
    exact ⟨m', by omega, c', hc'⟩

include hop in
/-- **Exact peeling.** If `f = h(x_i, g(rest))` for AND/OR `h` and nonconstant `g`, then
`min(f) = min(g) + 1`, in the counted-NOT basis and in the monotone basis. -/
theorem peel_contraction (hpeel : IsPeel op i f g) (hg : ∀ v, ¬ ∀ y, g y = v)
    (hfin : ∃ k, SizeLE b g k) : minSize b f = minSize b g + 1 := by
  refine minSize_eq_succ (peel_sizeLE hop i hpeel hg) ?_ hfin
  rintro ⟨m, hm, c, hw, hb, hc⟩
  obtain ⟨m', hm', -⟩ := peel_restriction hop i hpeel hg c hw hb hc
  omega

end Peel

end CircuitLemmas
