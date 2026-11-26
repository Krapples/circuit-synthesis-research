/-
Gate elimination in the free-NOT binary basis (2026-11-25).

Model. A circuit on `n` inputs is a straight-line program of fan-in-two AND gates whose operands are
literals: a constant, or a wire with a complement flag. Wires `0 .. n-1` are inputs and gate `j` is wire
`n + j`. Negations are free and OR is an AND with complemented operands and output, so the gate count is
the binary AIG count `B` used by Percy and in `NOTES_SAT_ENCODING_BOUNDS.md`. Gates are stored latest
first (`rgates`), which makes evaluation structurally recursive. A wire that does not exist yet reads
`false`, so no well-formedness side condition is needed. Assignments are `ℕ → Bool`; only inputs below
`n` are read.

Proved here:
* `bypass`: a gate whose value equals a literal over earlier wires can be deleted (size drops by one);
  `bypass_many` deletes all such gates at once, `delete_dead` deletes a gate nothing reads.
* `Circuit.eval_restrict`: fixing an input to a constant is a circuit of the same size.
* `realizes_restrict`: restriction does not increase complexity.
* `restrict_eliminates`: fixing input `z` deletes every gate that reads `z`.
* `literal_extension`: if `g` is nonconstant and ignores input `z`, then every circuit for `g ∧ x_z`
  has at least one gate more than some circuit for `g`, i.e. `C(g ∧ z) ≥ C(g) + 1`.
* `conditional_restriction`, `conditional_counter`: deleting gates keeps every function computed inside
  the circuit (`Lit`), so fixing `z := b` gives `|C| - #readers(z) ≥ M(f|_{z=b}, H)` for every set `H` of
  `z`-independent functions computed in `C` (multi-output cost with free phases, `RealizesWith`). This is
  the soundness of the forward conditional restriction counters (singleton and full-mask forms).
* `cascade_restriction`, `conditional_counter_cascade`: the same with the full cascade count, i.e. every
  gate with an operand that is constant under `z := b` (readers of `z`, then readers of gates the restriction
  forces constant, and so on) is deleted; `readers_le_cascade` shows this contains the first level.

The other foundations of the six-bit SAT bound (three-gate absorbing elimination, excess monotonicity,
`C(F_q) = 4q - 1`, the string identities) are not formalized yet.
-/
import Mathlib

namespace CircuitLemmas.GateElim

/-- An operand: a constant, or wire `w` complemented when `neg`. -/
inductive Ref where
  | const (b : Bool)
  | wire (w : ℕ) (neg : Bool)
  deriving DecidableEq

namespace Ref

def eval (v : ℕ → Bool) : Ref → Bool
  | const b => b
  | wire w neg => Bool.xor (v w) neg

/-- Complement a literal. -/
def negate (c : Bool) : Ref → Ref
  | const b => const (Bool.xor b c)
  | wire w neg => wire w (Bool.xor neg c)

theorem eval_negate (v : ℕ → Bool) (c : Bool) (r : Ref) :
    (r.negate c).eval v = Bool.xor (r.eval v) c := by
  cases r <;> simp [negate, eval]

/-- Does the literal read wire `z`? -/
def Reads (z : ℕ) : Ref → Prop
  | const _ => False
  | wire w _ => w = z

end Ref

/-- A binary AND gate on two literals. -/
structure Gate where
  a : Ref
  b : Ref

def Gate.eval (v : ℕ → Bool) (g : Gate) : Bool := g.a.eval v && g.b.eval v

/-- Wire values. `rgs` lists the gates latest first; the newest gate is wire `n + rgs.length - 1`. -/
def val (n : ℕ) (x : ℕ → Bool) : List Gate → ℕ → Bool
  | [], w => if w < n then x w else false
  | g :: rgs, w => if w = n + rgs.length then g.eval (val n x rgs) else val n x rgs w

structure Circuit where
  n : ℕ
  rgates : List Gate
  out : Ref

namespace Circuit

def size (C : Circuit) : ℕ := C.rgates.length

def eval (C : Circuit) (x : ℕ → Bool) : Bool := C.out.eval (val C.n x C.rgates)

end Circuit

/-- `f` has a circuit on `n` inputs with at most `s` binary gates. -/
def Realizes (n : ℕ) (f : (ℕ → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ C : Circuit, C.n = n ∧ C.size ≤ s ∧ ∀ x, C.eval x = f x

/-! ## Wire values -/

theorem val_input (n : ℕ) (x : ℕ → Bool) : ∀ (rgs : List Gate) (w : ℕ), w < n → val n x rgs w = x w
  | [], w, h => by simp [val, h]
  | g :: rgs, w, h => by
      simp only [val]
      rw [if_neg (by omega)]
      exact val_input n x rgs w h

theorem val_ge (n : ℕ) (x : ℕ → Bool) :
    ∀ (rgs : List Gate) (w : ℕ), n + rgs.length ≤ w → val n x rgs w = false
  | [], w, h => by
      simp only [List.length_nil, Nat.add_zero] at h
      simp only [val]
      rw [if_neg (by omega)]
  | g :: rgs, w, h => by
      simp only [List.length_cons] at h
      simp only [val]
      rw [if_neg (by omega)]
      exact val_ge n x rgs w (by omega)

theorem val_append_lt (n : ℕ) (x : ℕ → Bool) (earlier : List Gate) :
    ∀ (later : List Gate) (w : ℕ), w < n + earlier.length →
      val n x (later ++ earlier) w = val n x earlier w
  | [], _, _ => rfl
  | g :: later, w, h => by
      simp only [List.cons_append, val, List.length_append]
      rw [if_neg (by omega)]
      exact val_append_lt n x earlier later w h

/-! ## Deleting a gate that equals a literal -/

/-- Replace a literal that reads a missing wire (`≥ p`) by the constant it evaluates to. -/
def Ref.clip (p : ℕ) : Ref → Ref
  | const b => const b
  | wire w neg => if w < p then wire w neg else const neg

theorem Ref.clip_eval (n : ℕ) (x : ℕ → Bool) (earlier : List Gate) (r : Ref) :
    (r.clip (n + earlier.length)).eval (val n x earlier) = r.eval (val n x earlier) := by
  cases r with
  | const b => rfl
  | wire w neg =>
      by_cases h : w < n + earlier.length
      · simp [clip, h]
      · simp [clip, h, eval, val_ge n x earlier w (by omega)]

theorem Ref.clip_bound (p : ℕ) (r : Ref) : ∀ w neg, r.clip p = .wire w neg → w < p := by
  intro w neg h
  cases r with
  | const b => simp [clip] at h
  | wire w' neg' =>
      by_cases hw : w' < p
      · simp [clip, hw] at h; omega
      · simp [clip, hw] at h

/-- Renumber the wires after deleting wire `p`, reading `L` in its place. -/
def Ref.shift (r : Ref) (p : ℕ) (L : Ref) : Ref :=
  match r with
  | const b => const b
  | wire w neg => if w < p then wire w neg else if w = p then L.negate neg else wire (w - 1) neg

def Gate.shift (p : ℕ) (L : Ref) (g : Gate) : Gate := ⟨g.a.shift p L, g.b.shift p L⟩

section Bypass

variable (n : ℕ) (x : ℕ → Bool) (earlier : List Gate) (gj : Gate) (L : Ref)

/-- The values of the circuit without gate `p = n + earlier.length`. -/
abbrev V' (later : List Gate) : ℕ → Bool :=
  val n x (later.map (Gate.shift (n + earlier.length) L) ++ earlier)

/-- The values of the original circuit. -/
abbrev V (later : List Gate) : ℕ → Bool := val n x (later ++ gj :: earlier)

theorem bypass_lt (later : List Gate) (w : ℕ) (hw : w < n + earlier.length) :
    V' n x earlier L later w = V n x earlier gj later w := by
  simp only [V', V]
  rw [val_append_lt n x earlier _ w hw, val_append_lt n x (gj :: earlier) _ w (by simp; omega)]
  simp only [val]
  rw [if_neg (by omega)]

theorem bypass_at (hL : gj.eval (val n x earlier) = L.eval (val n x earlier))
    (hLb : ∀ w neg, L = .wire w neg → w < n + earlier.length) (later : List Gate) :
    L.eval (V' n x earlier L later) = V n x earlier gj later (n + earlier.length) := by
  simp only [V']
  have hL' : L.eval (val n x (later.map (Gate.shift (n + earlier.length) L) ++ earlier)) =
      L.eval (val n x earlier) := by
    cases L with
    | const b => rfl
    | wire w neg =>
        have := hLb w neg rfl
        simp [Ref.eval, val_append_lt n x earlier _ w this]
  rw [hL', ← hL]
  simp only [V]
  rw [val_append_lt n x (gj :: earlier) _ _ (by simp)]
  simp [val]

theorem bypass_ref (later : List Gate)
    (h_at : L.eval (V' n x earlier L later) = V n x earlier gj later (n + earlier.length))
    (h_gt : ∀ w, n + earlier.length < w →
      V' n x earlier L later (w - 1) = V n x earlier gj later w)
    (r : Ref) :
    (r.shift (n + earlier.length) L).eval (V' n x earlier L later) =
      r.eval (V n x earlier gj later) := by
  cases r with
  | const b => rfl
  | wire w neg =>
      simp only [Ref.shift]
      by_cases h1 : w < n + earlier.length
      · simp only [h1, if_true, Ref.eval]
        rw [bypass_lt n x earlier gj L later w h1]
      · by_cases h2 : w = n + earlier.length
        · subst h2
          simp only [h1, if_false, if_true]
          rw [Ref.eval_negate, h_at]
          rfl
        · simp only [h1, h2, if_false, Ref.eval]
          rw [h_gt w (by omega)]

theorem bypass_gt (hL : gj.eval (val n x earlier) = L.eval (val n x earlier))
    (hLb : ∀ w neg, L = .wire w neg → w < n + earlier.length) :
    ∀ (later : List Gate) (w : ℕ), n + earlier.length < w →
      V' n x earlier L later (w - 1) = V n x earlier gj later w
  | [], w, hw => by
      simp only [V', V, List.map_nil, List.nil_append]
      simp only [val]
      rw [if_neg (by omega), val_ge n x earlier w (by omega), val_ge n x earlier (w - 1) (by omega)]
  | g :: later, w, hw => by
      have ih := bypass_gt hL hLb later
      have hr := bypass_ref n x earlier gj L later (bypass_at n x earlier gj L hL hLb later) ih
      simp only [V', V, List.map_cons, List.cons_append, val, List.length_append, List.length_map,
        List.length_cons]
      by_cases htop : w = n + (later.length + (earlier.length + 1))
      · rw [if_pos (by omega), if_pos htop]
        simp only [Gate.eval, Gate.shift]
        rw [hr g.a, hr g.b]
      · rw [if_neg (by omega), if_neg htop]
        exact ih w hw

end Bypass

/-- The explicit circuit without gate `p = n + earlier.length`, which is read as the literal `L`. -/
def deleteGate (n : ℕ) (later earlier : List Gate) (out L : Ref) : Circuit :=
  let p := n + earlier.length
  ⟨n, later.map (Gate.shift p (L.clip p)) ++ earlier, out.shift p (L.clip p)⟩

theorem deleteGate_eval (n : ℕ) (later earlier : List Gate) (gj : Gate) (out L : Ref)
    (hL : ∀ x, gj.eval (val n x earlier) = L.eval (val n x earlier)) (x : ℕ → Bool) :
    (deleteGate n later earlier out L).eval x = (Circuit.mk n (later ++ gj :: earlier) out).eval x := by
  set p := n + earlier.length
  have hL' : gj.eval (val n x earlier) = (L.clip p).eval (val n x earlier) := by
    rw [hL x, Ref.clip_eval]
  have hb := Ref.clip_bound p L
  exact bypass_ref n x earlier gj (L.clip p) later (bypass_at n x earlier gj _ hL' hb later)
    (bypass_gt n x earlier gj _ hL' hb later) out

/-- Deleting a gate whose value is a literal over earlier wires (on every input) gives an equivalent
circuit with one gate fewer. -/
theorem bypass (C : Circuit) (later earlier : List Gate) (gj : Gate) (L : Ref)
    (hC : C.rgates = later ++ gj :: earlier)
    (hL : ∀ x, gj.eval (val C.n x earlier) = L.eval (val C.n x earlier)) :
    ∃ C' : Circuit, C'.n = C.n ∧ C'.size + 1 = C.size ∧ ∀ x, C'.eval x = C.eval x := by
  refine ⟨deleteGate C.n later earlier C.out L, rfl, ?_, fun x => ?_⟩
  · simp [deleteGate, Circuit.size, hC]; omega
  · rw [deleteGate_eval C.n later earlier gj C.out L hL x]
    obtain ⟨n, rgs, out⟩ := C
    simp only at hC
    subst hC
    rfl

/-! ## Dead gates -/

theorem Ref.eval_congr (v v' : ℕ → Bool) (p : ℕ) (r : Ref) (hr : ¬ r.Reads p)
    (h : ∀ w, w ≠ p → v w = v' w) : r.eval v = r.eval v' := by
  cases r with
  | const b => rfl
  | wire w neg => simp only [Ref.Reads] at hr; simp [Ref.eval, h w hr]

/-- Replacing a gate that no later gate reads leaves every other wire unchanged. -/
theorem val_replace_dead (n : ℕ) (x : ℕ → Bool) (earlier : List Gate) (gj g' : Gate) :
    ∀ later : List Gate, (∀ g ∈ later, ¬ g.a.Reads (n + earlier.length) ∧ ¬ g.b.Reads (n + earlier.length)) →
      ∀ w, w ≠ n + earlier.length →
        val n x (later ++ g' :: earlier) w = val n x (later ++ gj :: earlier) w
  | [], _, w, hw => by simp only [List.nil_append, val]; rw [if_neg hw, if_neg hw]
  | g :: later, hdead, w, hw => by
      have ih := val_replace_dead n x earlier gj g' later (fun g hg => hdead g (List.mem_cons_of_mem _ hg))
      obtain ⟨ha, hb⟩ := hdead g List.mem_cons_self
      simp only [List.cons_append, val, List.length_append, List.length_cons]
      split_ifs
      · simp only [Gate.eval]
        rw [Ref.eval_congr _ _ _ g.a ha ih, Ref.eval_congr _ _ _ g.b hb ih]
      · exact ih w hw

/-- A gate that no later gate and not the output reads can be deleted. -/
theorem delete_dead (C : Circuit) (later earlier : List Gate) (gj : Gate)
    (hC : C.rgates = later ++ gj :: earlier)
    (hdead : ∀ g ∈ later, ¬ g.a.Reads (C.n + earlier.length) ∧ ¬ g.b.Reads (C.n + earlier.length))
    (hout : ¬ C.out.Reads (C.n + earlier.length)) :
    ∃ C' : Circuit, C'.n = C.n ∧ C'.size + 1 = C.size ∧ ∀ x, C'.eval x = C.eval x := by
  -- replace the dead gate by the constant gate `false ∧ false`, then bypass it
  let g' : Gate := ⟨.const false, .const false⟩
  obtain ⟨C', hn, hs, he⟩ := bypass ⟨C.n, later ++ g' :: earlier, C.out⟩ later earlier g' (.const false) rfl
    (fun x => by simp [g', Gate.eval, Ref.eval])
  refine ⟨C', hn, by simp [Circuit.size, hC] at hs ⊢; omega, fun x => ?_⟩
  rw [he x]
  simp only [Circuit.eval, hC]
  exact Ref.eval_congr _ _ _ C.out hout (val_replace_dead C.n x earlier gj g' later hdead)

/-! ## Functions computed inside a circuit -/

/-- `h` is a literal (a constant, or a possibly complemented wire) over the wires of `rgs`: some input or
gate computes `h` or its complement, or `h` is constant. -/
def Lit (n : ℕ) (rgs : List Gate) (h : (ℕ → Bool) → Bool) : Prop :=
  ∃ r : Ref, (∀ w neg, r = .wire w neg → w < n + rgs.length) ∧ ∀ x, r.eval (val n x rgs) = h x

theorem Ref.negate_wire {c : Bool} {r : Ref} {w : ℕ} {neg : Bool} (h : r.negate c = .wire w neg) :
    ∃ neg0, r = .wire w neg0 := by
  cases r with
  | const b => simp [Ref.negate] at h
  | wire w' n' =>
      simp only [Ref.negate, Ref.wire.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact ⟨n', rfl⟩

/-- Deleting a gate that equals a literal keeps every function computed inside the circuit. -/
theorem lit_delete (n : ℕ) (later earlier : List Gate) (gj : Gate) (L : Ref)
    (hL : ∀ x, gj.eval (val n x earlier) = L.eval (val n x earlier)) (h : (ℕ → Bool) → Bool)
    (hl : Lit n (later ++ gj :: earlier) h) :
    Lit n (later.map (Gate.shift (n + earlier.length) (L.clip (n + earlier.length))) ++ earlier) h := by
  set p := n + earlier.length with hp
  obtain ⟨r, hb, hr⟩ := hl
  refine ⟨r.shift p (L.clip p), ?_, fun x => ?_⟩
  · intro w neg hw
    simp only [List.length_append, List.length_map]
    cases r with
    | const c => simp [Ref.shift] at hw
    | wire w0 neg0 =>
        have hb0 := hb w0 neg0 rfl
        simp only [List.length_append, List.length_cons] at hb0
        simp only [Ref.shift] at hw
        split_ifs at hw with h1 h2
        · simp only [Ref.wire.injEq] at hw
          obtain ⟨rfl, -⟩ := hw
          omega
        · obtain ⟨neg1, h3⟩ := Ref.negate_wire hw
          have := Ref.clip_bound p L w neg1 h3
          omega
        · simp only [Ref.wire.injEq] at hw
          obtain ⟨rfl, -⟩ := hw
          omega
  · have hL' : gj.eval (val n x earlier) = (L.clip p).eval (val n x earlier) := by
      rw [hL x, Ref.clip_eval]
    have hcb := Ref.clip_bound p L
    rw [← hr x]
    exact bypass_ref n x earlier gj (L.clip p) later (bypass_at n x earlier gj _ hL' hcb later)
      (bypass_gt n x earlier gj _ hL' hcb later) r

/-! ## Deleting several gates -/

/-- Gate `g`, placed after the gates `earlier`, equals a literal over earlier wires on every input. -/
def Degenerate (n : ℕ) (g : Gate) (earlier : List Gate) : Prop :=
  ∃ L : Ref, ∀ x, g.eval (val n x earlier) = L.eval (val n x earlier)

open Classical in
/-- The number of degenerate gates of a gate list (latest first). -/
noncomputable def degCount (n : ℕ) : List Gate → ℕ
  | [] => 0
  | g :: rgs => (if Degenerate n g rgs then 1 else 0) + degCount n rgs

/-- All degenerate gates can be deleted together: delete the latest first, which leaves the prefixes
of the earlier ones unchanged. Every function computed inside the circuit stays computed. -/
theorem bypass_many (n : ℕ) :
    ∀ (rest later : List Gate) (out : Ref), ∃ C' : Circuit, C'.n = n ∧
      C'.size + degCount n rest ≤ (later ++ rest).length ∧
      (∀ x, C'.eval x = (Circuit.mk n (later ++ rest) out).eval x) ∧
      ∀ h, Lit n (later ++ rest) h → Lit n C'.rgates h
  | [], later, out => ⟨⟨n, later, out⟩, rfl, by simp [Circuit.size, degCount], fun _ => by simp,
      fun _ hl => by simpa using hl⟩
  | g :: rest, later, out => by
      by_cases hd : Degenerate n g rest
      · have hd' := hd
        obtain ⟨L, hL⟩ := hd
        set p := n + rest.length
        obtain ⟨C', hn, hs, he, hlit⟩ :=
          bypass_many n rest (later.map (Gate.shift p (L.clip p))) (out.shift p (L.clip p))
        refine ⟨C', hn, ?_, fun x => ?_, fun h hl => hlit h (lit_delete n later rest g L hL h hl)⟩
        · simp only [degCount, if_pos hd', List.length_append, List.length_map,
            List.length_cons] at hs ⊢
          omega
        · rw [he x, ← deleteGate_eval n later rest g out L hL x]
          rfl
      · obtain ⟨C', hn, hs, he, hlit⟩ := bypass_many n rest (later ++ [g]) out
        refine ⟨C', hn, ?_, fun x => ?_, fun h hl => hlit h (by simpa using hl)⟩
        · simp only [degCount, if_neg hd, List.length_append, List.length_cons,
            List.length_nil] at hs ⊢
          omega
        · rw [he x]; simp

/-! ## Restrictions -/

/-- `x` with input `i` set to `b`. -/
def upd (x : ℕ → Bool) (i : ℕ) (b : Bool) : ℕ → Bool := fun w => if w = i then b else x w

@[simp] theorem upd_same (x : ℕ → Bool) (i : ℕ) (b : Bool) : upd x i b i = b := by simp [upd]

@[simp] theorem upd_upd (x : ℕ → Bool) (i : ℕ) (b c : Bool) : upd (upd x i b) i c = upd x i c := by
  funext w; by_cases h : w = i <;> simp [upd, h]

def Ref.restrict (i : ℕ) (b : Bool) : Ref → Ref
  | const c => const c
  | wire w neg => if w = i then const (Bool.xor b neg) else wire w neg

def Gate.restrict (i : ℕ) (b : Bool) (g : Gate) : Gate := ⟨g.a.restrict i b, g.b.restrict i b⟩

def Circuit.restrict (C : Circuit) (i : ℕ) (b : Bool) : Circuit :=
  ⟨C.n, C.rgates.map (Gate.restrict i b), C.out.restrict i b⟩

theorem restrict_ref (n : ℕ) (x : ℕ → Bool) (i : ℕ) (b : Bool) (hi : i < n) (rgs : List Gate)
    (h : ∀ w, w ≠ i → val n x (rgs.map (Gate.restrict i b)) w = val n (upd x i b) rgs w) (r : Ref) :
    (r.restrict i b).eval (val n x (rgs.map (Gate.restrict i b))) = r.eval (val n (upd x i b) rgs) := by
  cases r with
  | const c => rfl
  | wire w neg =>
      by_cases hw : w = i
      · subst hw; simp [Ref.restrict, Ref.eval, val_input n _ rgs w hi]
      · simp [Ref.restrict, hw, Ref.eval, h w hw]

theorem restrict_val (n : ℕ) (x : ℕ → Bool) (i : ℕ) (b : Bool) (hi : i < n) :
    ∀ (rgs : List Gate) (w : ℕ), w ≠ i →
      val n x (rgs.map (Gate.restrict i b)) w = val n (upd x i b) rgs w
  | [], w, hw => by simp [val, upd, hw]
  | g :: rgs, w, hw => by
      have ih := restrict_val n x i b hi rgs
      simp only [List.map_cons, val, List.length_map]
      by_cases htop : w = n + rgs.length
      · rw [if_pos htop, if_pos htop]
        simp only [Gate.eval, Gate.restrict]
        rw [restrict_ref n x i b hi rgs ih g.a, restrict_ref n x i b hi rgs ih g.b]
      · rw [if_neg htop, if_neg htop]
        exact ih w hw

theorem Circuit.eval_restrict (C : Circuit) (i : ℕ) (b : Bool) (hi : i < C.n) (x : ℕ → Bool) :
    (C.restrict i b).eval x = C.eval (upd x i b) :=
  restrict_ref C.n x i b hi C.rgates (restrict_val C.n x i b hi C.rgates) C.out

theorem Circuit.size_restrict (C : Circuit) (i : ℕ) (b : Bool) : (C.restrict i b).size = C.size := by
  simp [Circuit.restrict, Circuit.size]

/-- Fixing an input does not increase complexity. -/
theorem realizes_restrict {n s : ℕ} {f : (ℕ → Bool) → Bool} (i : ℕ) (b : Bool) (hi : i < n)
    (h : Realizes n f s) : Realizes n (fun x => f (upd x i b)) s := by
  obtain ⟨C, hn, hs, hf⟩ := h
  refine ⟨C.restrict i b, hn, by rw [Circuit.size_restrict]; exact hs, fun x => ?_⟩
  rw [Circuit.eval_restrict C i b (hn ▸ hi), hf]

theorem Ref.restrict_of_not_reads (i : ℕ) (b : Bool) (r : Ref) (h : ¬ r.Reads i) :
    r.restrict i b = r := by
  cases r with
  | const c => rfl
  | wire w neg => simp [Ref.Reads] at h; simp [Ref.restrict, h]

/-- A circuit in which no operand reads input `i` does not depend on it. -/
theorem Circuit.eval_upd_of_not_reads (C : Circuit) (i : ℕ) (b : Bool) (hi : i < C.n)
    (hg : ∀ g ∈ C.rgates, ¬ g.a.Reads i ∧ ¬ g.b.Reads i) (ho : ¬ C.out.Reads i) (x : ℕ → Bool) :
    C.eval (upd x i b) = C.eval x := by
  have hC : C.restrict i b = C := by
    obtain ⟨n, rgs, out⟩ := C
    simp only [Circuit.restrict, Circuit.mk.injEq, true_and]
    refine ⟨?_, Ref.restrict_of_not_reads i b out ho⟩
    conv_rhs => rw [← List.map_id rgs]
    refine List.map_congr_left fun g hg' => ?_
    obtain ⟨ha, hb⟩ := hg g hg'
    simp [Gate.restrict, Ref.restrict_of_not_reads i b _ ha, Ref.restrict_of_not_reads i b _ hb]
  rw [← Circuit.eval_restrict C i b hi, hC]

/-! ## Each reader of a fixed input disappears -/

/-- A gate with a constant operand equals a literal. -/
theorem Gate.eval_const_left (c : Bool) (r : Ref) :
    ∃ L : Ref, ∀ v, (Gate.mk (.const c) r).eval v = L.eval v :=
  ⟨if c then r else .const false, fun v => by cases c <;> simp [Gate.eval, Ref.eval]⟩

theorem Gate.eval_const_right (c : Bool) (r : Ref) :
    ∃ L : Ref, ∀ v, (Gate.mk r (.const c)).eval v = L.eval v :=
  ⟨if c then r else .const false, fun v => by cases c <;> simp [Gate.eval, Ref.eval]⟩

/-- A gate that reads `z`, with `z` fixed, equals a literal. -/
theorem Gate.restrict_literal (z : ℕ) (b : Bool) (g : Gate) (h : g.a.Reads z ∨ g.b.Reads z) :
    ∃ L : Ref, ∀ v, (g.restrict z b).eval v = L.eval v := by
  obtain ⟨a, bb⟩ := g
  rcases h with ha | hb
  · cases a with
    | const c => simp [Ref.Reads] at ha
    | wire w neg =>
        simp only [Ref.Reads] at ha; subst ha
        simpa [Gate.restrict, Ref.restrict] using Gate.eval_const_left (Bool.xor b neg) (bb.restrict w b)
  · cases bb with
    | const c => simp [Ref.Reads] at hb
    | wire w neg =>
        simp only [Ref.Reads] at hb; subst hb
        simpa [Gate.restrict, Ref.restrict] using Gate.eval_const_right (Bool.xor b neg) (a.restrict w b)

open Classical in
/-- The number of gates that read wire `z`. -/
noncomputable def readers (z : ℕ) (rgs : List Gate) : ℕ :=
  (rgs.filter fun g => decide (g.a.Reads z ∨ g.b.Reads z)).length

theorem degCount_restrict (n z : ℕ) (b : Bool) :
    ∀ rgs : List Gate, readers z rgs ≤ degCount n (rgs.map (Gate.restrict z b))
  | [] => by simp [readers, degCount]
  | g :: rgs => by
      have ih := degCount_restrict n z b rgs
      by_cases hr : g.a.Reads z ∨ g.b.Reads z
      · have hd : Degenerate n (g.restrict z b) (rgs.map (Gate.restrict z b)) := by
          obtain ⟨L, hL⟩ := Gate.restrict_literal z b g hr
          exact ⟨L, fun x => hL _⟩
        simp only [readers, List.filter_cons, hr, decide_true, if_true, List.length_cons,
          List.map_cons, degCount, hd] at ih ⊢
        omega
      · simp only [readers, List.filter_cons, hr, decide_false, List.map_cons, degCount] at ih ⊢
        split_ifs <;> simp only [Bool.false_eq_true] at * <;> omega

/-- **Gate elimination by a constant.** Fixing input `z` deletes every gate that reads it. -/
theorem restrict_eliminates (C : Circuit) (z : ℕ) (b : Bool) (hz : z < C.n) :
    ∃ C' : Circuit, C'.n = C.n ∧ C'.size + readers z C.rgates ≤ C.size ∧
      ∀ x, C'.eval x = C.eval (upd x z b) := by
  obtain ⟨C', hn, hs, he, -⟩ := bypass_many C.n (C.rgates.map (Gate.restrict z b)) [] (C.out.restrict z b)
  refine ⟨C', hn, ?_, fun x => ?_⟩
  · have := degCount_restrict C.n z b C.rgates
    simp only [List.nil_append, List.length_map, Circuit.size] at hs ⊢
    omega
  · rw [he x, ← Circuit.eval_restrict C z b hz]
    rfl

/-! ## Conditional restriction counters -/

/-- Restriction maps a function computed inside the circuit to its restriction. -/
theorem lit_restrict (n i : ℕ) (b : Bool) (hi : i < n) (rgs : List Gate) (h : (ℕ → Bool) → Bool)
    (hl : Lit n rgs h) : Lit n (rgs.map (Gate.restrict i b)) (fun x => h (upd x i b)) := by
  obtain ⟨r, hb, hr⟩ := hl
  refine ⟨r.restrict i b, fun w neg hw => ?_, fun x => ?_⟩
  · cases r with
    | const c => simp [Ref.restrict] at hw
    | wire w0 neg0 =>
        by_cases h1 : w0 = i <;> simp [Ref.restrict, h1] at hw
        obtain ⟨rfl, rfl⟩ := hw
        simpa using hb w0 neg0 rfl
  · rw [restrict_ref n x i b hi rgs (restrict_val n x i b hi rgs) r, hr]

/-- **Restriction with surviving functions.** Fixing input `z` deletes every reader of `z`, and every
function computed inside the circuit survives, restricted. -/
theorem conditional_restriction (C : Circuit) (z : ℕ) (b : Bool) (hz : z < C.n) :
    ∃ C' : Circuit, C'.n = C.n ∧ C'.size + readers z C.rgates ≤ C.size ∧
      (∀ x, C'.eval x = C.eval (upd x z b)) ∧
      ∀ h, Lit C.n C.rgates h → Lit C.n C'.rgates (fun x => h (upd x z b)) := by
  obtain ⟨C', hn, hs, he, hlit⟩ :=
    bypass_many C.n (C.rgates.map (Gate.restrict z b)) [] (C.out.restrict z b)
  refine ⟨C', hn, ?_, fun x => ?_, fun h hl => hlit _ (by simpa using lit_restrict C.n z b hz C.rgates h hl)⟩
  · have := degCount_restrict C.n z b C.rgates
    simp only [List.nil_append, List.length_map, Circuit.size] at hs ⊢
    omega
  · rw [he x, ← Circuit.eval_restrict C z b hz]
    rfl

/-- `f` has a circuit with at most `s` gates inside which every `h ∈ H` is computed (as a literal over its
wires): the multi-output cost `M(f, H)` with free output phases is the least such `s`. -/
def RealizesWith (n : ℕ) (f : (ℕ → Bool) → Bool) (H : Set ((ℕ → Bool) → Bool)) (s : ℕ) : Prop :=
  ∃ C : Circuit, C.n = n ∧ C.size ≤ s ∧ (∀ x, C.eval x = f x) ∧ ∀ h ∈ H, Lit n C.rgates h

/-- A gate of the circuit computes a function inside it. -/
theorem lit_of_gate (n : ℕ) (rgs : List Gate) (w : ℕ) (hw : w < n + rgs.length) :
    Lit n rgs (fun x => val n x rgs w) :=
  ⟨.wire w false, fun w' neg h => by simp only [Ref.wire.injEq] at h; omega, fun x => by simp [Ref.eval]⟩

/-- **Conditional restriction counter.** Let `C` compute `f`, fix input `z := b`, and let `H` be functions
computed inside `C` that do not depend on `z` (for example first-layer gates on two other inputs). Then
`|C| - #readers(z) ≥ M(f|_{z=b}, H)`. In the SAT encoding the left side is at most `k - D`, where `D`
counts gates with a provably constant operand, and those gates read `z` or are later readers of constants;
this file proves the first-level form. With `H = {h}` and `M(f|, {h}) = L + 1` this is the singleton clause
`¬presence(h) ∨ survivors ≥ L + 1`. -/
theorem conditional_counter {n : ℕ} {f : (ℕ → Bool) → Bool} (C : Circuit) (hn : C.n = n)
    (hf : ∀ x, C.eval x = f x) (z : ℕ) (b : Bool) (hz : z < n) (H : Set ((ℕ → Bool) → Bool))
    (hH : ∀ h ∈ H, Lit n C.rgates h) (hindep : ∀ h ∈ H, ∀ x c, h (upd x z c) = h x) :
    RealizesWith n (fun x => f (upd x z b)) H (C.size - readers z C.rgates) := by
  subst hn
  obtain ⟨C', hn', hs, he, hlit⟩ := conditional_restriction C z b hz
  refine ⟨C', hn', by omega, fun x => by rw [he, hf], fun h hh => ?_⟩
  have hl := hlit h (hH h hh)
  have e : (fun x => h (upd x z b)) = h := funext fun x => hindep h hh x b
  rwa [e] at hl

/-! ## Independent literal extension -/

/-- **Independent literal extension.** If `g` is nonconstant and does not depend on input `z`, then
from any circuit for `g ∧ x_z` with `s` gates one gets a circuit for `g` with `s - 1` gates. Fix
`x_z := 1`; some gate reads `x_z` (otherwise the circuit ignores `x_z`, or its output is the literal
`x_z`), and that gate becomes a literal, which `bypass` deletes. -/
theorem literal_extension {n s z : ℕ} (hz : z < n) (g : (ℕ → Bool) → Bool)
    (hindep : ∀ x c, g (upd x z c) = g x) (h1 : ∃ x, g x = true) (h0 : ∃ x, g x = false)
    (h : Realizes n (fun x => g x && x z) s) : Realizes n g (s - 1) := by
  obtain ⟨C, hn, hs, hf⟩ := h
  have hzC : z < C.n := hn ▸ hz
  by_cases hread : ∃ gj ∈ C.rgates, gj.a.Reads z ∨ gj.b.Reads z
  · obtain ⟨gj, hmem, hgj⟩ := hread
    obtain ⟨later, earlier, hsplit⟩ := List.append_of_mem hmem
    set C1 := C.restrict z true
    have hC1 : C1.rgates = later.map (Gate.restrict z true) ++
        Gate.restrict z true gj :: earlier.map (Gate.restrict z true) := by
      simp [C1, Circuit.restrict, hsplit]
    -- the restricted gate has a constant operand, so it is a literal
    obtain ⟨L, hL⟩ : ∃ L : Ref, ∀ v, (Gate.restrict z true gj).eval v = L.eval v := by
      obtain ⟨a, b⟩ := gj
      rcases hgj with ha | hb
      · cases a with
        | const c => simp [Ref.Reads] at ha
        | wire w neg =>
            simp only [Ref.Reads] at ha; subst ha
            simpa [Gate.restrict, Ref.restrict] using
              Gate.eval_const_left (Bool.xor true neg) (b.restrict w true)
      · cases b with
        | const c => simp [Ref.Reads] at hb
        | wire w neg =>
            simp only [Ref.Reads] at hb; subst hb
            simpa [Gate.restrict, Ref.restrict] using
              Gate.eval_const_right (Bool.xor true neg) (a.restrict w true)
    obtain ⟨C', hn', hsize, heval⟩ := bypass C1 _ _ _ L hC1 (fun x => hL _)
    refine ⟨C', hn'.trans hn, ?_, fun x => ?_⟩
    · have : C1.size = C.size := Circuit.size_restrict C z true
      omega
    · rw [heval, Circuit.eval_restrict C z true hzC, hf]
      simp only [hindep, upd_same, Bool.and_true]
  · simp only [not_exists, not_and, not_or] at hread
    have hg : ∀ gj ∈ C.rgates, ¬ gj.a.Reads z ∧ ¬ gj.b.Reads z := fun gj hm =>
      not_or.mp (fun hor => by rcases hor with ha | hb; exact (hread gj hm).1 ha; exact (hread gj hm).2 hb)
    by_cases ho : C.out.Reads z
    · -- the output is the literal x_z (possibly complemented): contradicts g ≢ 1
      exfalso
      obtain ⟨x0, hx0⟩ := h0
      cases hout : C.out with
      | const c => rw [hout] at ho; simp [Ref.Reads] at ho
      | wire w neg =>
          rw [hout] at ho; simp only [Ref.Reads] at ho; subst ho
          have e := hf (upd x0 w (!neg))
          simp only [Circuit.eval, hout, Ref.eval, val_input C.n _ C.rgates w hzC, upd_same,
            hindep, hx0] at e
          cases neg <;> simp at e
    · -- the circuit ignores x_z: contradicts g ≢ 0
      exfalso
      obtain ⟨x1, hx1⟩ := h1
      have e1 := hf (upd x1 z true)
      have e0 := hf (upd x1 z false)
      rw [Circuit.eval_upd_of_not_reads C z _ hzC hg ho] at e1 e0
      simp only [hindep, hx1, upd_same, Bool.and_true, Bool.and_false] at e1 e0
      rw [e1] at e0
      exact absurd e0 (by decide)

/-! ## Cascaded constant deletions -/

/-- Wire `w` of `rgs` is constant once input `z` is fixed to `b`. Input `z` is such a wire, and so is every
gate whose value the restriction forces. -/
def ConstUnder (n z : ℕ) (b : Bool) (rgs : List Gate) (w : ℕ) : Prop :=
  ∃ c, ∀ x, val n (upd x z b) rgs w = c

/-- The operand reads a wire that is constant under `z := b`. -/
def Ref.ReadsConst (n z : ℕ) (b : Bool) (rgs : List Gate) : Ref → Prop
  | .const _ => False
  | .wire w _ => ConstUnder n z b rgs w

open Classical in
/-- Gates (latest first) with an operand that is constant under `z := b`: the readers of `z` and, in
cascade, the readers of gates that the restriction forces constant. -/
noncomputable def cascade (n z : ℕ) (b : Bool) : List Gate → ℕ
  | [] => 0
  | g :: rgs => (if g.a.ReadsConst n z b rgs ∨ g.b.ReadsConst n z b rgs then 1 else 0) + cascade n z b rgs

theorem restrict_gate_eval (n z : ℕ) (b : Bool) (hz : z < n) (x : ℕ → Bool) (rgs : List Gate) (g : Gate) :
    (g.restrict z b).eval (val n x (rgs.map (Gate.restrict z b))) = g.eval (val n (upd x z b) rgs) := by
  simp only [Gate.eval, Gate.restrict]
  rw [restrict_ref n x z b hz rgs (restrict_val n x z b hz rgs) g.a,
    restrict_ref n x z b hz rgs (restrict_val n x z b hz rgs) g.b]

/-- A gate with an operand that is constant under the restriction becomes a literal. -/
theorem degenerate_of_readsConst (n z : ℕ) (b : Bool) (hz : z < n) (rgs : List Gate) (g : Gate)
    (h : g.a.ReadsConst n z b rgs ∨ g.b.ReadsConst n z b rgs) :
    Degenerate n (g.restrict z b) (rgs.map (Gate.restrict z b)) := by
  have hR := fun x => restrict_ref n x z b hz rgs (restrict_val n x z b hz rgs)
  obtain ⟨a, bb⟩ := g
  rcases h with ha | hb
  · cases a with
    | const c => simp [Ref.ReadsConst] at ha
    | wire w neg =>
        obtain ⟨c, hc⟩ := ha
        refine ⟨if Bool.xor c neg then bb.restrict z b else .const false, fun x => ?_⟩
        rw [restrict_gate_eval n z b hz x rgs]
        cases hcn : Bool.xor c neg
        · simp [Gate.eval, Ref.eval, hc, hcn]
        · simp only [hcn, ↓reduceIte]
          rw [hR x bb]
          simp [Gate.eval, Ref.eval, hc, hcn]
  · cases bb with
    | const c => simp [Ref.ReadsConst] at hb
    | wire w neg =>
        obtain ⟨c, hc⟩ := hb
        refine ⟨if Bool.xor c neg then a.restrict z b else .const false, fun x => ?_⟩
        rw [restrict_gate_eval n z b hz x rgs]
        cases hcn : Bool.xor c neg
        · simp [Gate.eval, Ref.eval, hc, hcn]
        · simp only [hcn, ↓reduceIte]
          rw [hR x a]
          simp [Gate.eval, Ref.eval, hc, hcn]

theorem degCount_cascade (n z : ℕ) (b : Bool) (hz : z < n) :
    ∀ rgs : List Gate, cascade n z b rgs ≤ degCount n (rgs.map (Gate.restrict z b))
  | [] => by simp [cascade, degCount]
  | g :: rgs => by
      have ih := degCount_cascade n z b hz rgs
      by_cases hr : g.a.ReadsConst n z b rgs ∨ g.b.ReadsConst n z b rgs
      · have hd := degenerate_of_readsConst n z b hz rgs g hr
        simp only [cascade, if_pos hr, List.map_cons, degCount, if_pos hd]
        omega
      · simp only [cascade, if_neg hr, List.map_cons, degCount]
        split_ifs <;> omega

/-- The cascade count contains every reader of `z`. -/
theorem readers_le_cascade (n z : ℕ) (b : Bool) (hz : z < n) :
    ∀ rgs : List Gate, readers z rgs ≤ cascade n z b rgs
  | [] => by simp [readers, cascade]
  | g :: rgs => by
      have ih := readers_le_cascade n z b hz rgs
      have key : ∀ r : Ref, r.Reads z → r.ReadsConst n z b rgs := by
        intro r hr
        cases r with
        | const c => simp [Ref.Reads] at hr
        | wire w neg =>
            simp only [Ref.Reads] at hr; subst hr
            exact ⟨b, fun x => by rw [val_input n _ rgs w hz, upd_same]⟩
      by_cases hr : g.a.Reads z ∨ g.b.Reads z
      · have hc : g.a.ReadsConst n z b rgs ∨ g.b.ReadsConst n z b rgs := hr.imp (key _) (key _)
        simp only [readers, List.filter_cons, hr, decide_true, if_true, List.length_cons] at ih ⊢
        simp only [cascade, if_pos hc]
        omega
      · simp only [readers, List.filter_cons, hr, decide_false] at ih ⊢
        simp only [cascade]
        split_ifs <;> simp only [Bool.false_eq_true] at * <;> omega

/-- **Cascaded constant deletions.** Fixing `z := b` deletes every gate with an operand that is constant under
the restriction: the readers of `z`, the readers of gates that the restriction forces constant, and so on.
Every function computed inside the circuit survives, restricted. This is the full cascade count `D` of the
conditional restriction counters; `conditional_restriction` is the first level. -/
theorem cascade_restriction (C : Circuit) (z : ℕ) (b : Bool) (hz : z < C.n) :
    ∃ C' : Circuit, C'.n = C.n ∧ C'.size + cascade C.n z b C.rgates ≤ C.size ∧
      (∀ x, C'.eval x = C.eval (upd x z b)) ∧
      ∀ h, Lit C.n C.rgates h → Lit C.n C'.rgates (fun x => h (upd x z b)) := by
  obtain ⟨C', hn, hs, he, hlit⟩ :=
    bypass_many C.n (C.rgates.map (Gate.restrict z b)) [] (C.out.restrict z b)
  refine ⟨C', hn, ?_, fun x => ?_, fun h hl => hlit _ (by simpa using lit_restrict C.n z b hz C.rgates h hl)⟩
  · have := degCount_cascade C.n z b hz C.rgates
    simp only [List.nil_append, List.length_map, Circuit.size] at hs ⊢
    omega
  · rw [he x, ← Circuit.eval_restrict C z b hz]
    rfl

/-- **Cascaded conditional counter.** As `conditional_counter`, with the full cascade count:
`|C| - cascade(z := b) ≥ M(f|_{z=b}, H)`. -/
theorem conditional_counter_cascade {n : ℕ} {f : (ℕ → Bool) → Bool} (C : Circuit) (hn : C.n = n)
    (hf : ∀ x, C.eval x = f x) (z : ℕ) (b : Bool) (hz : z < n) (H : Set ((ℕ → Bool) → Bool))
    (hH : ∀ h ∈ H, Lit n C.rgates h) (hindep : ∀ h ∈ H, ∀ x c, h (upd x z c) = h x) :
    RealizesWith n (fun x => f (upd x z b)) H (C.size - cascade n z b C.rgates) := by
  subst hn
  obtain ⟨C', hn', hs, he, hlit⟩ := cascade_restriction C z b hz
  refine ⟨C', hn', by omega, fun x => by rw [he, hf], fun h hh => ?_⟩
  have hl := hlit h (hH h hh)
  have e : (fun x => h (upd x z b)) = h := funext fun x => hindep h hh x b
  rwa [e] at hl

end CircuitLemmas.GateElim
