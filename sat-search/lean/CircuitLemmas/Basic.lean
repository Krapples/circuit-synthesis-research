/-
Circuit model and counting identities (pilot formalization, 2026-11-24).

Model (matches sat-search/cube_search.py and verify/reference.py): wires 0..n-1 are inputs, gate j is
wire n + j; a binary gate (AND/OR) reads two distinct earlier wires l < r, a NOT gate reads one earlier
wire. These are statements about the mathematical model, not about the Python implementation.
-/
import Mathlib

namespace CircuitLemmas

open Finset BigOperators

inductive Op
  | and
  | or
  | not
  deriving DecidableEq

structure Gate where
  op : Op
  l : ℕ
  r : ℕ

namespace Gate

/-- Binary gates read two wires, NOT reads one. -/
def arity (g : Gate) : ℕ := if g.op = Op.not then 1 else 2

/-- The wires a gate reads. -/
def reads (g : Gate) : Finset ℕ := if g.op = Op.not then {g.l} else {g.l, g.r}

def isBinary (g : Gate) : Prop := g.op ≠ Op.not

instance (g : Gate) : Decidable g.isBinary := inferInstanceAs (Decidable (g.op ≠ Op.not))

end Gate

/-- A circuit with `n` inputs and `m` gates. -/
structure Circuit (n m : ℕ) where
  gate : Fin m → Gate

namespace Circuit

variable {n m : ℕ} (c : Circuit n m)

/-- Gate `j` (wire `n + j`) reads earlier wires; a binary gate reads two distinct wires `l < r`. -/
def WellFormed : Prop :=
  ∀ j : Fin m, ((c.gate j).op = Op.not → (c.gate j).l < n + j) ∧
    ((c.gate j).op ≠ Op.not → (c.gate j).l < (c.gate j).r ∧ (c.gate j).r < n + j)

/-- Number of gates reading wire `w`. -/
def readCount (w : ℕ) : ℕ := (univ.filter fun j : Fin m => w ∈ (c.gate j).reads).card

/-- Number of binary gates. -/
def binaryCount : ℕ := (univ.filter fun j : Fin m => (c.gate j).isBinary).card

lemma reads_subset (hw : c.WellFormed) (j : Fin m) : (c.gate j).reads ⊆ range (n + m) := by
  intro w hwmem
  have hj := j.isLt
  obtain ⟨h1, h2⟩ := hw j
  unfold Gate.reads at hwmem
  split_ifs at hwmem with hop
  · rw [mem_singleton] at hwmem; subst hwmem; have := h1 hop; rw [mem_range]; omega
  · rw [mem_insert, mem_singleton] at hwmem
    have := h2 hop
    rw [mem_range]; rcases hwmem with rfl | rfl <;> omega

lemma card_reads (hw : c.WellFormed) (j : Fin m) : ((c.gate j).reads).card = (c.gate j).arity := by
  unfold Gate.reads Gate.arity
  split_ifs with hop
  · simp
  · have := ((hw j).2 hop).1
    exact card_pair (by omega)

/-- Read-count identity: the reads of all wires add up to the total arity (double counting). -/
theorem sum_readCount (hw : c.WellFormed) :
    ∑ w ∈ range (n + m), c.readCount w = ∑ j : Fin m, (c.gate j).arity := by
  unfold readCount
  simp_rw [card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [← sum_filter, ← card_eq_sum_ones, ← card_reads c hw j]
  congr 1
  ext w
  simp only [mem_filter, mem_range]
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h; exact ⟨mem_range.mp (reads_subset c hw j h), h⟩

/-- Total arity: two per binary gate, one per NOT gate. -/
lemma sum_arity : ∑ j : Fin m, (c.gate j).arity = 2 * c.binaryCount + (m - c.binaryCount) := by
  have hsplit := sum_filter_add_sum_filter_not (univ : Finset (Fin m)) (fun j => (c.gate j).isBinary)
    (fun j => (c.gate j).arity)
  rw [← hsplit]
  have hb : ∑ j ∈ univ.filter (fun j => (c.gate j).isBinary), (c.gate j).arity
      = 2 * c.binaryCount := by
    rw [binaryCount, card_eq_sum_ones, mul_sum, mul_one]
    refine sum_congr rfl fun j hj => ?_
    have h : (c.gate j).op ≠ Op.not := (mem_filter.mp hj).2
    simp [Gate.arity, h]
  have hn : ∑ j ∈ univ.filter (fun j => ¬ (c.gate j).isBinary), (c.gate j).arity
      = m - c.binaryCount := by
    have hc : (univ.filter fun j : Fin m => ¬ (c.gate j).isBinary).card = m - c.binaryCount := by
      have h := card_filter_add_card_filter_not (s := (univ : Finset (Fin m)))
        (fun j => (c.gate j).isBinary)
      rw [card_univ, Fintype.card_fin] at h
      unfold binaryCount
      omega
    rw [← hc, card_eq_sum_ones]
    refine sum_congr rfl fun j hj => ?_
    have h : (c.gate j).op = Op.not := by
      have := (mem_filter.mp hj).2
      simpa [Gate.isBinary] using this
    simp [Gate.arity, h]
  rw [hb, hn]

/-- Connectivity lower bound: if every wire except the output is read, the circuit has at least
`n - 1` binary gates (equivalently, the excess fan-out `B - n + 1` is nonnegative). -/
theorem connectivity (hw : c.WellFormed) (hm : 1 ≤ m)
    (hread : ∀ w < n + m - 1, 1 ≤ c.readCount w) : n ≤ c.binaryCount + 1 := by
  have hsum := sum_readCount c hw
  rw [sum_arity] at hsum
  have hlow : n + m - 1 ≤ ∑ w ∈ range (n + m), c.readCount w := by
    calc n + m - 1 = ∑ _w ∈ range (n + m - 1), 1 := by simp
      _ ≤ ∑ w ∈ range (n + m - 1), c.readCount w := sum_le_sum fun w hw' => hread w (mem_range.mp hw')
      _ ≤ ∑ w ∈ range (n + m), c.readCount w :=
          sum_le_sum_of_subset (range_mono (Nat.sub_le _ _))
  have hB : c.binaryCount ≤ m := by
    calc c.binaryCount ≤ (univ : Finset (Fin m)).card := card_filter_le _ _
      _ = m := by simp
  have h1 := hlow
  rw [hsum] at h1
  omega

/-- Excess fan-out identity: summing (reads - 1) over the non-output wires, all of which are read,
gives exactly `B - n + 1`, stated in ℤ. -/
theorem excess_identity (hw : c.WellFormed) (hm : 1 ≤ m) (hout : c.readCount (n + m - 1) = 0) :
    ∑ w ∈ range (n + m - 1), ((c.readCount w : ℤ) - 1) = (c.binaryCount : ℤ) - n + 1 := by
  have hsum := sum_readCount c hw
  rw [sum_arity] at hsum
  have hB : c.binaryCount ≤ m := by
    calc c.binaryCount ≤ (univ : Finset (Fin m)).card := card_filter_le _ _
      _ = m := by simp
  have hsplit : ∑ w ∈ range (n + m), c.readCount w
      = ∑ w ∈ range (n + m - 1), c.readCount w + c.readCount (n + m - 1) := by
    have : n + m = (n + m - 1) + 1 := by omega
    rw [this, sum_range_succ]; simp
  rw [hsplit, hout, add_zero] at hsum
  have hS : (∑ w ∈ range (n + m - 1), (c.readCount w : ℤ))
      = 2 * (c.binaryCount : ℤ) + ((m : ℤ) - c.binaryCount) := by
    have h : ((∑ w ∈ range (n + m - 1), c.readCount w : ℕ) : ℤ)
        = ((2 * c.binaryCount + (m - c.binaryCount) : ℕ) : ℤ) := by rw [hsum]
    push_cast [Nat.cast_sub hB] at h
    exact h
  rw [sum_sub_distrib, hS]
  simp only [sum_const, card_range, nsmul_eq_mul, mul_one]
  push_cast [Nat.cast_sub (show 1 ≤ n + m by omega)]
  ring

end Circuit

end CircuitLemmas
