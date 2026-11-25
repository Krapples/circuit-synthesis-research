
import Mathlib
import PEqualNP.Defs

namespace PG3LocalAudit
open PEqualNP.CircuitLowerBounds

def adj (u v : Fin 25) : Prop :=
  u.val < 12 ∧ 12 ≤ v.val ∧ (u.val + v.val + 2) % 13 ∈ ([0, 1, 3, 9] : List ℕ)

def edges : List (Fin 25 × Fin 25) := [(0, 12), (0, 14), (0, 20), (0, 24), (1, 13), (1, 19), (1, 23), (1, 24), (2, 12), (2, 18), (2, 22), (2, 23), (3, 17), (3, 21), (3, 22), (3, 24), (4, 16), (4, 20), (4, 21), (4, 23), (5, 15), (5, 19), (5, 20), (5, 22), (6, 14), (6, 18), (6, 19), (6, 21), (7, 13), (7, 17), (7, 18), (7, 20), (8, 12), (8, 16), (8, 17), (8, 19), (9, 15), (9, 16), (9, 18), (9, 24), (10, 14), (10, 15), (10, 17), (10, 23), (11, 13), (11, 14), (11, 16), (11, 22)]

def candidate : Circuit := ⟨[⟨.or, [12, 14]⟩, ⟨.or, [20, 24]⟩, ⟨.or, [25, 26]⟩, ⟨.and, [0, 27]⟩, ⟨.or, [13, 19]⟩, ⟨.or, [23, 24]⟩, ⟨.or, [29, 30]⟩, ⟨.and, [1, 31]⟩, ⟨.or, [12, 18]⟩, ⟨.or, [22, 23]⟩, ⟨.or, [33, 34]⟩, ⟨.and, [2, 35]⟩, ⟨.or, [17, 21]⟩, ⟨.or, [22, 24]⟩, ⟨.or, [37, 38]⟩, ⟨.and, [3, 39]⟩, ⟨.or, [16, 20]⟩, ⟨.or, [21, 23]⟩, ⟨.or, [41, 42]⟩, ⟨.and, [4, 43]⟩, ⟨.or, [15, 19]⟩, ⟨.or, [20, 22]⟩, ⟨.or, [45, 46]⟩, ⟨.and, [5, 47]⟩, ⟨.or, [14, 18]⟩, ⟨.or, [19, 21]⟩, ⟨.or, [49, 50]⟩, ⟨.and, [6, 51]⟩, ⟨.or, [13, 17]⟩, ⟨.or, [18, 20]⟩, ⟨.or, [53, 54]⟩, ⟨.and, [7, 55]⟩, ⟨.or, [12, 16]⟩, ⟨.or, [17, 19]⟩, ⟨.or, [57, 58]⟩, ⟨.and, [8, 59]⟩, ⟨.or, [15, 16]⟩, ⟨.or, [18, 24]⟩, ⟨.or, [61, 62]⟩, ⟨.and, [9, 63]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [17, 23]⟩, ⟨.or, [65, 66]⟩, ⟨.and, [10, 67]⟩, ⟨.or, [13, 14]⟩, ⟨.or, [16, 22]⟩, ⟨.or, [69, 70]⟩, ⟨.and, [11, 71]⟩, ⟨.or, [28, 32]⟩, ⟨.or, [73, 36]⟩, ⟨.or, [74, 40]⟩, ⟨.or, [75, 44]⟩, ⟨.or, [76, 48]⟩, ⟨.or, [77, 52]⟩, ⟨.or, [78, 56]⟩, ⟨.or, [79, 60]⟩, ⟨.or, [80, 64]⟩, ⟨.or, [81, 68]⟩, ⟨.or, [82, 72]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [15, 21]⟩, ⟨.or, [84, 85]⟩], 83⟩

theorem adjIff : ∀ u v : Fin 25, adj u v ↔ (u, v) ∈ edges := by
  unfold adj edges
  decide +kernel

theorem dist (x y z : Bool) : (x && (y || z)) = ((x && y) || (x && z)) := by
  cases x <;> rfl

def appendGate (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def stage0 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24]

theorem initial (x : Fin 25 → Bool) : List.ofFn x = stage0 x := by rfl

def v25 (x : Fin 25 → Bool) : Bool := GateOp.eval .or [x 12, x 14]

def stage1 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, v25 x]

theorem step1 (x : Fin 25 → Bool) : appendGate (stage0 x) ⟨.or, [12, 14]⟩ = stage1 x := by rfl

def v26 (x : Fin 25 → Bool) : Bool := GateOp.eval .or [x 20, x 24]

def stage2 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, v25 x, v26 x]

theorem step2 (x : Fin 25 → Bool) : appendGate (stage1 x) ⟨.or, [20, 24]⟩ = stage2 x := by rfl

def v27 (x : Fin 25 → Bool) : Bool := GateOp.eval .or [v25 x, v26 x]

def stage3 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, v25 x, v26 x, v27 x]

theorem step3 (x : Fin 25 → Bool) : appendGate (stage2 x) ⟨.or, [25, 26]⟩ = stage3 x := by rfl

def v28 (x : Fin 25 → Bool) : Bool := GateOp.eval .and [x 0, v27 x]

def stage4 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, v25 x, v26 x, v27 x, v28 x]

theorem step4 (x : Fin 25 → Bool) : appendGate (stage3 x) ⟨.and, [0, 27]⟩ = stage4 x := by rfl

def v29 (x : Fin 25 → Bool) : Bool := GateOp.eval .or [x 13, x 19]

def stage5 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, v25 x, v26 x, v27 x, v28 x, v29 x]

theorem step5 (x : Fin 25 → Bool) : appendGate (stage4 x) ⟨.or, [13, 19]⟩ = stage5 x := by rfl

def v30 (x : Fin 25 → Bool) : Bool := GateOp.eval .or [x 23, x 24]

def stage6 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x]

theorem step6 (x : Fin 25 → Bool) : appendGate (stage5 x) ⟨.or, [23, 24]⟩ = stage6 x := by rfl

def v31 (x : Fin 25 → Bool) : Bool := GateOp.eval .or [v29 x, v30 x]

def stage7 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x]

theorem step7 (x : Fin 25 → Bool) : appendGate (stage6 x) ⟨.or, [29, 30]⟩ = stage7 x := by rfl

def v32 (x : Fin 25 → Bool) : Bool := GateOp.eval .and [x 1, v31 x]

def stage8 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x]

theorem step8 (x : Fin 25 → Bool) : appendGate (stage7 x) ⟨.and, [1, 31]⟩ = stage8 x := by rfl

def v33 (x : Fin 25 → Bool) : Bool := GateOp.eval .or [x 12, x 18]

def stage9 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x]

theorem step9 (x : Fin 25 → Bool) : appendGate (stage8 x) ⟨.or, [12, 18]⟩ = stage9 x := by rfl

def v34 (x : Fin 25 → Bool) : Bool := GateOp.eval .or [x 22, x 23]

def stage10 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x]

theorem step10 (x : Fin 25 → Bool) : appendGate (stage9 x) ⟨.or, [22, 23]⟩ = stage10 x := by rfl

def v35 (x : Fin 25 → Bool) : Bool := GateOp.eval .or [v33 x, v34 x]

def stage11 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x]

theorem step11 (x : Fin 25 → Bool) : appendGate (stage10 x) ⟨.or, [33, 34]⟩ = stage11 x := by rfl

def v36 (x : Fin 25 → Bool) : Bool := GateOp.eval .and [x 2, v35 x]

def stage12 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x]

theorem step12 (x : Fin 25 → Bool) : appendGate (stage11 x) ⟨.and, [2, 35]⟩ = stage12 x := by rfl

def v37 (x : Fin 25 → Bool) : Bool := GateOp.eval .or [x 17, x 21]

def stage13 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x]

theorem step13 (x : Fin 25 → Bool) : appendGate (stage12 x) ⟨.or, [17, 21]⟩ = stage13 x := by rfl

def v38 (x : Fin 25 → Bool) : Bool := GateOp.eval .or [x 22, x 24]

def stage14 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x]

theorem step14 (x : Fin 25 → Bool) : appendGate (stage13 x) ⟨.or, [22, 24]⟩ = stage14 x := by rfl

def v39 (x : Fin 25 → Bool) : Bool := GateOp.eval .or [v37 x, v38 x]

def stage15 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x]

theorem step15 (x : Fin 25 → Bool) : appendGate (stage14 x) ⟨.or, [37, 38]⟩ = stage15 x := by rfl

def v40 (x : Fin 25 → Bool) : Bool := GateOp.eval .and [x 3, v39 x]

def stage16 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x]

theorem step16 (x : Fin 25 → Bool) : appendGate (stage15 x) ⟨.and, [3, 39]⟩ = stage16 x := by rfl

def v41 (x : Fin 25 → Bool) : Bool := GateOp.eval .or [x 16, x 20]

def stage17 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x]

theorem step17 (x : Fin 25 → Bool) : appendGate (stage16 x) ⟨.or, [16, 20]⟩ = stage17 x := by rfl

def v42 (x : Fin 25 → Bool) : Bool := GateOp.eval .or [x 21, x 23]

def stage18 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x]

theorem step18 (x : Fin 25 → Bool) : appendGate (stage17 x) ⟨.or, [21, 23]⟩ = stage18 x := by rfl

def v43 (x : Fin 25 → Bool) : Bool := GateOp.eval .or [v41 x, v42 x]

def stage19 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x]

theorem step19 (x : Fin 25 → Bool) : appendGate (stage18 x) ⟨.or, [41, 42]⟩ = stage19 x := by rfl

def v44 (x : Fin 25 → Bool) : Bool := GateOp.eval .and [x 4, v43 x]

def stage20 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x]

theorem step20 (x : Fin 25 → Bool) : appendGate (stage19 x) ⟨.and, [4, 43]⟩ = stage20 x := by rfl

def v45 (x : Fin 25 → Bool) : Bool := GateOp.eval .or [x 15, x 19]

def stage21 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x]

theorem step21 (x : Fin 25 → Bool) : appendGate (stage20 x) ⟨.or, [15, 19]⟩ = stage21 x := by rfl

def v46 (x : Fin 25 → Bool) : Bool := GateOp.eval .or [x 20, x 22]

def stage22 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x]

theorem step22 (x : Fin 25 → Bool) : appendGate (stage21 x) ⟨.or, [20, 22]⟩ = stage22 x := by rfl

def v47 (x : Fin 25 → Bool) : Bool := GateOp.eval .or [v45 x, v46 x]

def stage23 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x]

theorem step23 (x : Fin 25 → Bool) : appendGate (stage22 x) ⟨.or, [45, 46]⟩ = stage23 x := by rfl

def v48 (x : Fin 25 → Bool) : Bool := GateOp.eval .and [x 5, v47 x]

def stage24 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x]

theorem step24 (x : Fin 25 → Bool) : appendGate (stage23 x) ⟨.and, [5, 47]⟩ = stage24 x := by rfl

def v49 (x : Fin 25 → Bool) : Bool := GateOp.eval .or [x 14, x 18]

def stage25 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x]

theorem step25 (x : Fin 25 → Bool) : appendGate (stage24 x) ⟨.or, [14, 18]⟩ = stage25 x := by rfl

def v50 (x : Fin 25 → Bool) : Bool := GateOp.eval .or [x 19, x 21]

def stage26 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x]

theorem step26 (x : Fin 25 → Bool) : appendGate (stage25 x) ⟨.or, [19, 21]⟩ = stage26 x := by rfl

def v51 (x : Fin 25 → Bool) : Bool := GateOp.eval .or [v49 x, v50 x]

def stage27 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x]

theorem step27 (x : Fin 25 → Bool) : appendGate (stage26 x) ⟨.or, [49, 50]⟩ = stage27 x := by rfl

def v52 (x : Fin 25 → Bool) : Bool := GateOp.eval .and [x 6, v51 x]

def stage28 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x]

theorem step28 (x : Fin 25 → Bool) : appendGate (stage27 x) ⟨.and, [6, 51]⟩ = stage28 x := by rfl

def v53 (x : Fin 25 → Bool) : Bool := GateOp.eval .or [x 13, x 17]

def stage29 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x]

theorem step29 (x : Fin 25 → Bool) : appendGate (stage28 x) ⟨.or, [13, 17]⟩ = stage29 x := by rfl

def v54 (x : Fin 25 → Bool) : Bool := GateOp.eval .or [x 18, x 20]

def stage30 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x]

theorem step30 (x : Fin 25 → Bool) : appendGate (stage29 x) ⟨.or, [18, 20]⟩ = stage30 x := by rfl

def v55 (x : Fin 25 → Bool) : Bool := GateOp.eval .or [v53 x, v54 x]

def stage31 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x]

theorem step31 (x : Fin 25 → Bool) : appendGate (stage30 x) ⟨.or, [53, 54]⟩ = stage31 x := by rfl

def v56 (x : Fin 25 → Bool) : Bool := GateOp.eval .and [x 7, v55 x]

def stage32 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x]

theorem step32 (x : Fin 25 → Bool) : appendGate (stage31 x) ⟨.and, [7, 55]⟩ = stage32 x := by rfl

def v57 (x : Fin 25 → Bool) : Bool := GateOp.eval .or [x 12, x 16]

def stage33 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x]

theorem step33 (x : Fin 25 → Bool) : appendGate (stage32 x) ⟨.or, [12, 16]⟩ = stage33 x := by rfl

def v58 (x : Fin 25 → Bool) : Bool := GateOp.eval .or [x 17, x 19]

def stage34 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x]

theorem step34 (x : Fin 25 → Bool) : appendGate (stage33 x) ⟨.or, [17, 19]⟩ = stage34 x := by rfl

def v59 (x : Fin 25 → Bool) : Bool := GateOp.eval .or [v57 x, v58 x]

def stage35 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x]

theorem step35 (x : Fin 25 → Bool) : appendGate (stage34 x) ⟨.or, [57, 58]⟩ = stage35 x := by rfl

def v60 (x : Fin 25 → Bool) : Bool := GateOp.eval .and [x 8, v59 x]

def stage36 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x]

theorem step36 (x : Fin 25 → Bool) : appendGate (stage35 x) ⟨.and, [8, 59]⟩ = stage36 x := by rfl

def v61 (x : Fin 25 → Bool) : Bool := GateOp.eval .or [x 15, x 16]

def stage37 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x]

theorem step37 (x : Fin 25 → Bool) : appendGate (stage36 x) ⟨.or, [15, 16]⟩ = stage37 x := by rfl

def v62 (x : Fin 25 → Bool) : Bool := GateOp.eval .or [x 18, x 24]

def stage38 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x]

theorem step38 (x : Fin 25 → Bool) : appendGate (stage37 x) ⟨.or, [18, 24]⟩ = stage38 x := by rfl

def v63 (x : Fin 25 → Bool) : Bool := GateOp.eval .or [v61 x, v62 x]

def stage39 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x]

theorem step39 (x : Fin 25 → Bool) : appendGate (stage38 x) ⟨.or, [61, 62]⟩ = stage39 x := by rfl

def v64 (x : Fin 25 → Bool) : Bool := GateOp.eval .and [x 9, v63 x]

def stage40 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x]

theorem step40 (x : Fin 25 → Bool) : appendGate (stage39 x) ⟨.and, [9, 63]⟩ = stage40 x := by rfl

def v65 (x : Fin 25 → Bool) : Bool := GateOp.eval .or [x 14, x 15]

def stage41 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x, v65 x]

theorem step41 (x : Fin 25 → Bool) : appendGate (stage40 x) ⟨.or, [14, 15]⟩ = stage41 x := by rfl

def v66 (x : Fin 25 → Bool) : Bool := GateOp.eval .or [x 17, x 23]

def stage42 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x, v65 x, v66 x]

theorem step42 (x : Fin 25 → Bool) : appendGate (stage41 x) ⟨.or, [17, 23]⟩ = stage42 x := by rfl

def v67 (x : Fin 25 → Bool) : Bool := GateOp.eval .or [v65 x, v66 x]

def stage43 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x, v65 x, v66 x, v67 x]

theorem step43 (x : Fin 25 → Bool) : appendGate (stage42 x) ⟨.or, [65, 66]⟩ = stage43 x := by rfl

def v68 (x : Fin 25 → Bool) : Bool := GateOp.eval .and [x 10, v67 x]

def stage44 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x, v65 x, v66 x, v67 x, v68 x]

theorem step44 (x : Fin 25 → Bool) : appendGate (stage43 x) ⟨.and, [10, 67]⟩ = stage44 x := by rfl

def v69 (x : Fin 25 → Bool) : Bool := GateOp.eval .or [x 13, x 14]

def stage45 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x, v65 x, v66 x, v67 x, v68 x, v69 x]

theorem step45 (x : Fin 25 → Bool) : appendGate (stage44 x) ⟨.or, [13, 14]⟩ = stage45 x := by rfl

def v70 (x : Fin 25 → Bool) : Bool := GateOp.eval .or [x 16, x 22]

def stage46 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x, v65 x, v66 x, v67 x, v68 x, v69 x, v70 x]

theorem step46 (x : Fin 25 → Bool) : appendGate (stage45 x) ⟨.or, [16, 22]⟩ = stage46 x := by rfl

def v71 (x : Fin 25 → Bool) : Bool := GateOp.eval .or [v69 x, v70 x]

def stage47 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x, v65 x, v66 x, v67 x, v68 x, v69 x, v70 x, v71 x]

theorem step47 (x : Fin 25 → Bool) : appendGate (stage46 x) ⟨.or, [69, 70]⟩ = stage47 x := by rfl

def v72 (x : Fin 25 → Bool) : Bool := GateOp.eval .and [x 11, v71 x]

def stage48 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x, v65 x, v66 x, v67 x, v68 x, v69 x, v70 x, v71 x, v72 x]

theorem step48 (x : Fin 25 → Bool) : appendGate (stage47 x) ⟨.and, [11, 71]⟩ = stage48 x := by rfl

def v73 (x : Fin 25 → Bool) : Bool := GateOp.eval .or [v28 x, v32 x]

def stage49 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x, v65 x, v66 x, v67 x, v68 x, v69 x, v70 x, v71 x, v72 x, v73 x]

theorem step49 (x : Fin 25 → Bool) : appendGate (stage48 x) ⟨.or, [28, 32]⟩ = stage49 x := by rfl

def v74 (x : Fin 25 → Bool) : Bool := GateOp.eval .or [v73 x, v36 x]

def stage50 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x, v65 x, v66 x, v67 x, v68 x, v69 x, v70 x, v71 x, v72 x, v73 x, v74 x]

theorem step50 (x : Fin 25 → Bool) : appendGate (stage49 x) ⟨.or, [73, 36]⟩ = stage50 x := by rfl

def v75 (x : Fin 25 → Bool) : Bool := GateOp.eval .or [v74 x, v40 x]

def stage51 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x, v65 x, v66 x, v67 x, v68 x, v69 x, v70 x, v71 x, v72 x, v73 x, v74 x, v75 x]

theorem step51 (x : Fin 25 → Bool) : appendGate (stage50 x) ⟨.or, [74, 40]⟩ = stage51 x := by rfl

def v76 (x : Fin 25 → Bool) : Bool := GateOp.eval .or [v75 x, v44 x]

def stage52 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x, v65 x, v66 x, v67 x, v68 x, v69 x, v70 x, v71 x, v72 x, v73 x, v74 x, v75 x, v76 x]

theorem step52 (x : Fin 25 → Bool) : appendGate (stage51 x) ⟨.or, [75, 44]⟩ = stage52 x := by rfl

def v77 (x : Fin 25 → Bool) : Bool := GateOp.eval .or [v76 x, v48 x]

def stage53 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x, v65 x, v66 x, v67 x, v68 x, v69 x, v70 x, v71 x, v72 x, v73 x, v74 x, v75 x, v76 x, v77 x]

theorem step53 (x : Fin 25 → Bool) : appendGate (stage52 x) ⟨.or, [76, 48]⟩ = stage53 x := by rfl

def v78 (x : Fin 25 → Bool) : Bool := GateOp.eval .or [v77 x, v52 x]

def stage54 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x, v65 x, v66 x, v67 x, v68 x, v69 x, v70 x, v71 x, v72 x, v73 x, v74 x, v75 x, v76 x, v77 x, v78 x]

theorem step54 (x : Fin 25 → Bool) : appendGate (stage53 x) ⟨.or, [77, 52]⟩ = stage54 x := by rfl

def v79 (x : Fin 25 → Bool) : Bool := GateOp.eval .or [v78 x, v56 x]

def stage55 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x, v65 x, v66 x, v67 x, v68 x, v69 x, v70 x, v71 x, v72 x, v73 x, v74 x, v75 x, v76 x, v77 x, v78 x, v79 x]

theorem step55 (x : Fin 25 → Bool) : appendGate (stage54 x) ⟨.or, [78, 56]⟩ = stage55 x := by rfl

def v80 (x : Fin 25 → Bool) : Bool := GateOp.eval .or [v79 x, v60 x]

def stage56 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x, v65 x, v66 x, v67 x, v68 x, v69 x, v70 x, v71 x, v72 x, v73 x, v74 x, v75 x, v76 x, v77 x, v78 x, v79 x, v80 x]

theorem step56 (x : Fin 25 → Bool) : appendGate (stage55 x) ⟨.or, [79, 60]⟩ = stage56 x := by rfl

def v81 (x : Fin 25 → Bool) : Bool := GateOp.eval .or [v80 x, v64 x]

def stage57 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x, v65 x, v66 x, v67 x, v68 x, v69 x, v70 x, v71 x, v72 x, v73 x, v74 x, v75 x, v76 x, v77 x, v78 x, v79 x, v80 x, v81 x]

theorem step57 (x : Fin 25 → Bool) : appendGate (stage56 x) ⟨.or, [80, 64]⟩ = stage57 x := by rfl

def v82 (x : Fin 25 → Bool) : Bool := GateOp.eval .or [v81 x, v68 x]

def stage58 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x, v65 x, v66 x, v67 x, v68 x, v69 x, v70 x, v71 x, v72 x, v73 x, v74 x, v75 x, v76 x, v77 x, v78 x, v79 x, v80 x, v81 x, v82 x]

theorem step58 (x : Fin 25 → Bool) : appendGate (stage57 x) ⟨.or, [81, 68]⟩ = stage58 x := by rfl

def v83 (x : Fin 25 → Bool) : Bool := GateOp.eval .or [v82 x, v72 x]

def stage59 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x, v65 x, v66 x, v67 x, v68 x, v69 x, v70 x, v71 x, v72 x, v73 x, v74 x, v75 x, v76 x, v77 x, v78 x, v79 x, v80 x, v81 x, v82 x, v83 x]

theorem step59 (x : Fin 25 → Bool) : appendGate (stage58 x) ⟨.or, [82, 72]⟩ = stage59 x := by rfl

def v84 (x : Fin 25 → Bool) : Bool := GateOp.eval .or [x 12, x 13]

def stage60 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x, v65 x, v66 x, v67 x, v68 x, v69 x, v70 x, v71 x, v72 x, v73 x, v74 x, v75 x, v76 x, v77 x, v78 x, v79 x, v80 x, v81 x, v82 x, v83 x, v84 x]

theorem step60 (x : Fin 25 → Bool) : appendGate (stage59 x) ⟨.or, [12, 13]⟩ = stage60 x := by rfl

def v85 (x : Fin 25 → Bool) : Bool := GateOp.eval .or [x 15, x 21]

def stage61 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x, v65 x, v66 x, v67 x, v68 x, v69 x, v70 x, v71 x, v72 x, v73 x, v74 x, v75 x, v76 x, v77 x, v78 x, v79 x, v80 x, v81 x, v82 x, v83 x, v84 x, v85 x]

theorem step61 (x : Fin 25 → Bool) : appendGate (stage60 x) ⟨.or, [15, 21]⟩ = stage61 x := by rfl

def v86 (x : Fin 25 → Bool) : Bool := GateOp.eval .or [v84 x, v85 x]

def stage62 (x : Fin 25 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x, v65 x, v66 x, v67 x, v68 x, v69 x, v70 x, v71 x, v72 x, v73 x, v74 x, v75 x, v76 x, v77 x, v78 x, v79 x, v80 x, v81 x, v82 x, v83 x, v84 x, v85 x, v86 x]

theorem step62 (x : Fin 25 → Bool) : appendGate (stage61 x) ⟨.or, [84, 85]⟩ = stage62 x := by rfl

theorem allWires (x : Fin 25 → Bool) : candidate.wires (List.ofFn x) = stage62 x := by
  change candidate.gates.foldl appendGate (List.ofFn x) = stage62 x
  rw [initial]
  simp only [candidate, List.foldl_cons, List.foldl_nil,
    step1, step2, step3, step4, step5, step6, step7, step8, step9, step10, step11, step12, step13, step14, step15, step16, step17, step18, step19, step20, step21, step22, step23, step24, step25, step26, step27, step28, step29, step30, step31, step32, step33, step34, step35, step36, step37, step38, step39, step40, step41, step42, step43, step44, step45, step46, step47, step48, step49, step50, step51, step52, step53, step54, step55, step56, step57, step58, step59, step60, step61, step62]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem evalWitness (x : Fin 25 → Bool) :
    candidate.eval (List.ofFn x) = edges.any (fun i => x i.1 && x i.2) := by
  unfold Circuit.eval
  rw [allWires]
  change v83 x = _
  simp [v25, v26, v27, v28, v29, v30, v31, v32, v33, v34, v35, v36, v37, v38, v39, v40, v41, v42, v43, v44, v45, v46, v47, v48, v49, v50, v51, v52, v53, v54, v55, v56, v57, v58, v59, v60, v61, v62, v63, v64, v65, v66, v67, v68, v69, v70, v71, v72, v73, v74, v75, v76, v77, v78, v79, v80, v81, v82, v83, GateOp.eval, edges, dist, Bool.or_assoc]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem proxyWitness (x : Fin 25 → Bool) :
    (candidate.wires (List.ofFn x)).getD 86 false = (x 12 || x 13 || x 15 || x 21) := by
  rw [allWires]
  change v86 x = _
  simp [v86, v85, v84, GateOp.eval, Bool.or_assoc]

theorem basisWitness : PEqualNP.MetaComplexity.Monotone2 candidate := by
  intro g hg
  simp only [candidate, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem localUpper62 :
    ∃ (C : Circuit) (w : ℕ), PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 62 ∧
      C.output < 25 + C.size ∧ w < 25 + C.size ∧
      ∀ x : Fin 25 → Bool,
        (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 25, adj u v ∧ x u = true ∧ x v = true) ∧
        (C.eval (List.ofFn x) = false → (C.wires (List.ofFn x)).getD w false = (x 12 || x 13 || x 15 || x 21)) := by
  refine ⟨candidate, 86, basisWitness, by decide, by decide, by decide, ?_⟩
  intro x
  refine ⟨?_, fun _ => proxyWitness x⟩
  rw [evalWitness, List.any_eq_true]
  constructor
  · rintro ⟨⟨u,v⟩, he, hx⟩
    have both : x u = true ∧ x v = true := by simpa using hx
    exact ⟨u, v, (adjIff u v).mpr he, both.1, both.2⟩
  · rintro ⟨u, v, he, hx, hy⟩
    exact ⟨(u,v), (adjIff u v).mp he, by simp [hx,hy]⟩

end PG3LocalAudit

#print axioms PG3LocalAudit.localUpper62
