/-
Model transfer (2026-11-26): a fan-in-two AND/OR/NOT circuit of the external pequalnp library
(`PEqualNP.CircuitLowerBounds.Circuit`, NOT gates counted) of size `s` gives a circuit of the repository's
free-NOT binary AIG model (`CircuitLemmas.GateElim`) with at most `s` gates for the same function.

Each external wire is tracked as a literal of the AIG. A binary AND gate becomes one AIG gate, a binary OR
gate one AIG gate with complemented operands and output, and NOT, unary and nullary gates become literals
with no gate. Wires that do not exist read `false` in both models.
-/
import PEqualNP.Defs.CircuitLowerBounds
import CircuitLemmas.GateElim

namespace SatBridge

open CircuitLemmas.GateElim

/-- The literal standing for external wire `i` (`false` when there is no such wire). -/
def opRef (refs : List Ref) (i : ℕ) : Ref := refs.getD i (.const false)

/-- Translate one external gate. The state is the AIG gates (latest first) and one literal per
external wire. -/
def step (n : ℕ) (st : List Gate × List Ref) (g : PEqualNP.CircuitLowerBounds.Gate) :
    List Gate × List Ref :=
  match g.op, g.inputs with
  | .and, [] => (st.1, st.2 ++ [.const true])
  | .and, [i] => (st.1, st.2 ++ [opRef st.2 i])
  | .and, [i, j] => (⟨opRef st.2 i, opRef st.2 j⟩ :: st.1, st.2 ++ [.wire (n + st.1.length) false])
  | .or, [] => (st.1, st.2 ++ [.const false])
  | .or, [i] => (st.1, st.2 ++ [opRef st.2 i])
  | .or, [i, j] =>
      (⟨(opRef st.2 i).negate true, (opRef st.2 j).negate true⟩ :: st.1,
        st.2 ++ [.wire (n + st.1.length) true])
  | .not, [] => (st.1, st.2 ++ [.const true])
  | .not, i :: _ => (st.1, st.2 ++ [(opRef st.2 i).negate true])
  | _, _ => (st.1, st.2 ++ [.const false])

/-- The gate is an AND, OR or NOT gate with at most two inputs. -/
def Ok (g : PEqualNP.CircuitLowerBounds.Gate) : Prop :=
  g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or,
    PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
    g.inputs.length ≤ 2

/-- Every wire a literal mentions exists. -/
def Scoped (p : ℕ) (r : Ref) : Prop := ∀ v neg, r = .wire v neg → v < p

/-- The invariant: one literal per external wire, each scoped, each with the external value. -/
def Inv (n : ℕ) (x : ℕ → Bool) (st : List Gate × List Ref) (w : List Bool) : Prop :=
  st.2.length = w.length ∧ (∀ r ∈ st.2, Scoped (n + st.1.length) r) ∧
    ∀ i, (opRef st.2 i).eval (val n x st.1) = w.getD i false

theorem opRef_mem (refs : List Ref) (i : ℕ) :
    opRef refs i = .const false ∨ opRef refs i ∈ refs := by
  unfold opRef
  by_cases h : i < refs.length
  · right; rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem h
  · left; rw [List.getD_eq_default _ _ (by omega)]

theorem scoped_opRef {p : ℕ} {refs : List Ref} (h : ∀ r ∈ refs, Scoped p r) (i : ℕ) :
    Scoped p (opRef refs i) := by
  rcases opRef_mem refs i with e | e
  · rw [e]; intro v neg hv; cases hv
  · exact h _ e

theorem scoped_negate {p : ℕ} {r : Ref} (h : Scoped p r) (c : Bool) : Scoped p (r.negate c) := by
  intro v neg hv
  cases r with
  | const b => cases hv
  | wire w ng =>
      simp only [Ref.negate, Ref.wire.injEq] at hv
      obtain ⟨rfl, -⟩ := hv
      exact h _ ng rfl

theorem scoped_mono {p p' : ℕ} {r : Ref} (h : Scoped p r) (hp : p ≤ p') : Scoped p' r :=
  fun v neg hv => lt_of_lt_of_le (h v neg hv) hp

/-- Adding a gate does not change the value of a scoped literal. -/
theorem eval_cons {n : ℕ} {x : ℕ → Bool} {rgs : List Gate} (G : Gate) {r : Ref}
    (h : Scoped (n + rgs.length) r) : r.eval (val n x (G :: rgs)) = r.eval (val n x rgs) := by
  cases r with
  | const b => rfl
  | wire v neg =>
      have hv := h v neg rfl
      simp only [Ref.eval, val]
      rw [if_neg (by omega)]

theorem opRef_append (refs : List Ref) (r : Ref) (i : ℕ) :
    opRef (refs ++ [r]) i =
      if i < refs.length then opRef refs i else if i = refs.length then r else .const false := by
  unfold opRef
  split_ifs with h1 h2
  · rw [List.getD_append _ _ _ _ h1]
  · subst h2; simp
  · rw [List.getD_eq_default _ _ (by simp; omega)]

theorem getD_append_one (w : List Bool) (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false = if i < w.length then w.getD i false else if i = w.length then b else false := by
  split_ifs with h1 h2
  · rw [List.getD_append _ _ _ _ h1]
  · subst h2; simp
  · rw [List.getD_eq_default _ _ (by simp; omega)]

/-- Extending by one literal with the right value keeps the invariant (no new gate). -/
theorem inv_lit {n : ℕ} {x : ℕ → Bool} {rgs : List Gate} {refs : List Ref} {w : List Bool}
    (h : Inv n x (rgs, refs) w) (r : Ref) (b : Bool) (hs : Scoped (n + rgs.length) r)
    (hv : r.eval (val n x rgs) = b) : Inv n x (rgs, refs ++ [r]) (w ++ [b]) := by
  obtain ⟨hl, hsc, hev⟩ := h
  refine ⟨by simp [hl], ?_, ?_⟩
  · intro r' hr'
    rcases List.mem_append.1 hr' with h' | h'
    · exact hsc r' h'
    · rw [List.mem_singleton.1 h']; exact hs
  · intro i
    simp only at hev hsc ⊢
    rw [opRef_append, getD_append_one, hl]
    split_ifs with h1 h2
    · exact hev i
    · exact hv
    · rfl

/-- Extending by a new gate whose output literal has the right value keeps the invariant. -/
theorem inv_gate {n : ℕ} {x : ℕ → Bool} {rgs : List Gate} {refs : List Ref} {w : List Bool}
    (h : Inv n x (rgs, refs) w) (G : Gate) (neg b : Bool)
    (hG : Bool.xor (G.eval (val n x rgs)) neg = b) :
    Inv n x (G :: rgs, refs ++ [.wire (n + rgs.length) neg]) (w ++ [b]) := by
  obtain ⟨hl, hsc, hev⟩ := h
  simp only at hl hsc hev
  refine ⟨by simp [hl], ?_, ?_⟩
  · intro r' hr'
    rcases List.mem_append.1 hr' with h' | h'
    · exact scoped_mono (hsc r' h') (by simp)
    · rw [List.mem_singleton.1 h']; intro v ng hv
      simp only [Ref.wire.injEq] at hv; simp; omega
  · intro i
    simp only
    rw [opRef_append, getD_append_one, hl]
    split_ifs with h1 h2
    · rw [eval_cons G (scoped_opRef hsc i)]; exact hev i
    · simp only [Ref.eval, val, if_pos rfl]; exact hG
    · rfl

theorem inv_step {n : ℕ} {x : ℕ → Bool} {st : List Gate × List Ref} {w : List Bool}
    (h : Inv n x st w) (g : PEqualNP.CircuitLowerBounds.Gate) (hg : Ok g) :
    Inv n x (step n st g) (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) ∧
      (step n st g).1.length ≤ st.1.length + 1 := by
  obtain ⟨rgs, refs⟩ := st
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  have hsc := h.2.1
  have hev := h.2.2
  simp only at hsc hev hop hlen
  have sc : ∀ i, Scoped (n + rgs.length) (opRef refs i) := scoped_opRef hsc
  have nc : ∀ b, Scoped (n + rgs.length) (Ref.const b) := fun b v neg hv => by cases hv
  rcases hop with rfl | rfl | rfl
  · match ins, hlen with
    | [], _ =>
        exact ⟨inv_lit h _ _ (nc true) (by simp [Ref.eval, PEqualNP.CircuitLowerBounds.GateOp.eval]),
          by simp [step]⟩
    | [i], _ =>
        exact ⟨inv_lit h _ _ (sc i) (by simp [hev, PEqualNP.CircuitLowerBounds.GateOp.eval]),
          by simp [step]⟩
    | [i, j], _ =>
        refine ⟨inv_gate h _ false _ ?_, by simp [step]⟩
        simp [Gate.eval, hev, PEqualNP.CircuitLowerBounds.GateOp.eval]
    | _ :: _ :: _ :: _, hl => simp at hl
  · match ins, hlen with
    | [], _ =>
        exact ⟨inv_lit h _ _ (nc false) (by simp [Ref.eval, PEqualNP.CircuitLowerBounds.GateOp.eval]),
          by simp [step]⟩
    | [i], _ =>
        exact ⟨inv_lit h _ _ (sc i) (by simp [hev, PEqualNP.CircuitLowerBounds.GateOp.eval]),
          by simp [step]⟩
    | [i, j], _ =>
        refine ⟨inv_gate h _ true _ ?_, by simp [step]⟩
        simp only [Gate.eval, Ref.eval_negate, hev, PEqualNP.CircuitLowerBounds.GateOp.eval,
          List.map_cons, List.map_nil, List.any_cons, List.any_nil]
        cases w.getD i false <;> cases w.getD j false <;> rfl
    | _ :: _ :: _ :: _, hl => simp at hl
  · match ins with
    | [] =>
        exact ⟨inv_lit h _ _ (nc true) (by simp [Ref.eval, PEqualNP.CircuitLowerBounds.GateOp.eval]),
          by simp [step]⟩
    | i :: _ =>
        exact ⟨inv_lit h _ _ (scoped_negate (sc i) true)
          (by simp [Ref.eval_negate, hev, PEqualNP.CircuitLowerBounds.GateOp.eval]), by simp [step]⟩

theorem inv_foldl {n : ℕ} {x : ℕ → Bool} :
    ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (st : List Gate × List Ref) (w : List Bool),
      (∀ g ∈ gs, Ok g) → Inv n x st w →
        Inv n x (gs.foldl (step n) st)
            (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w) ∧
          (gs.foldl (step n) st).1.length ≤ st.1.length + gs.length
  | [], st, w, _, h => ⟨h, by simp⟩
  | g :: gs, st, w, hok, h => by
      obtain ⟨h1, h2⟩ := inv_step h g (hok g (by simp))
      obtain ⟨h3, h4⟩ := inv_foldl gs _ _ (fun g' hg' => hok g' (by simp [hg'])) h1
      refine ⟨h3, ?_⟩
      simp only [List.foldl_cons, List.length_cons] at h4 ⊢
      omega

/-- The translated AIG. -/
def translate (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) : Circuit :=
  let st := C.gates.foldl (step n) ([], (List.range n).map fun i => .wire i false)
  ⟨n, st.1, opRef st.2 C.output⟩

theorem inv_init (n : ℕ) (x : ℕ → Bool) :
    Inv n x ([], (List.range n).map fun i => .wire i false)
      (List.ofFn fun i : Fin n => x i) := by
  refine ⟨by simp, ?_, ?_⟩
  · intro r hr v neg hv
    simp only [List.mem_map, List.mem_range] at hr
    obtain ⟨i, hi, rfl⟩ := hr
    simp only [Ref.wire.injEq] at hv
    simp; omega
  · intro i
    by_cases hi : i < n
    · have e : opRef ((List.range n).map fun i => Ref.wire i false) i = .wire i false := by
        unfold opRef; rw [List.getD_eq_getElem _ _ (by simpa using hi)]; simp
      rw [e, List.getD_eq_getElem _ _ (by simpa using hi)]
      simp [Ref.eval, val, hi]
    · have e : opRef ((List.range n).map fun i => Ref.wire i false) i = .const false := by
        unfold opRef; rw [List.getD_eq_default _ _ (by simp; omega)]
      rw [e, List.getD_eq_default _ _ (by simp; omega)]
      rfl

/-- **Model transfer.** A fan-in-two AND/OR/NOT circuit of the external library with `C.size` gates
(NOT gates included) gives an AIG with at most `C.size` binary gates computing the same function of the
first `n` inputs. -/
theorem transfer (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (hC : ∀ g ∈ C.gates, Ok g) :
    Realizes n (fun x => C.eval (List.ofFn fun i : Fin n => x i)) C.size := by
  refine ⟨translate n C, rfl, ?_, ?_⟩
  · have := (inv_foldl C.gates _ _ hC (inv_init n (fun _ => false))).2
    simpa [translate, Circuit.size, PEqualNP.CircuitLowerBounds.Circuit.size] using this
  · intro x
    have := (inv_foldl C.gates _ _ hC (inv_init n x)).1.2.2 C.output
    simpa [translate, Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.eval,
      PEqualNP.CircuitLowerBounds.Circuit.wires] using this

end SatBridge
