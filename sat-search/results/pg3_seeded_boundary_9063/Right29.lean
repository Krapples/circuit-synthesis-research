import Mathlib
import PEqualNP.Defs
import PEqualNP.Defs.TopForm

open PEqualNP.CircuitLowerBounds

namespace PLane9063

def graph (p l : Fin 13) : Prop :=
  l ∈ ([3, 4, 7, 8, 9, 10] : List (Fin 13)) ∧
    (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9)

instance (p l : Fin 13) : Decidable (graph p l) := by
  unfold graph
  infer_instance

def edges : List (Fin 26 × Fin 26) := [(3, 16), (4, 16), (6, 16), (12, 16), (0, 17), (4, 17), (5, 17), (7, 17), (3, 20), (7, 20), (8, 20), (10, 20), (4, 21), (8, 21), (9, 21), (11, 21), (5, 22), (9, 22), (10, 22), (12, 22), (0, 23), (6, 23), (10, 23), (11, 23)]
def witness : Circuit := ⟨[⟨.or, [3, 4]⟩, ⟨.or, [6, 12]⟩, ⟨.or, [27, 28]⟩, ⟨.and, [16, 29]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [5, 7]⟩, ⟨.or, [31, 32]⟩, ⟨.and, [17, 33]⟩, ⟨.or, [3, 7]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [35, 36]⟩, ⟨.and, [20, 37]⟩, ⟨.or, [4, 8]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [39, 40]⟩, ⟨.and, [21, 41]⟩, ⟨.or, [5, 9]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [43, 44]⟩, ⟨.and, [22, 45]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [47, 48]⟩, ⟨.and, [23, 49]⟩, ⟨.or, [30, 34]⟩, ⟨.or, [51, 38]⟩, ⟨.or, [52, 42]⟩, ⟨.or, [53, 46]⟩, ⟨.or, [54, 50]⟩], 55⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 6000000 in
theorem edgesExactly (p l : Fin 13) :
    graph p l ↔ (Fin.castAdd 13 p, Fin.natAdd 13 l) ∈ edges := by
  fin_cases p <;> fin_cases l <;> decide

theorem edgesOrigins (uv : Fin 26 × Fin 26) (hu : uv ∈ edges) :
    ∃ p l : Fin 13, graph p l ∧ uv = (Fin.castAdd 13 p, Fin.natAdd 13 l) := by
  simp only [edges, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨3, 3, by decide, rfl⟩
  · exact ⟨4, 3, by decide, rfl⟩
  · exact ⟨6, 3, by decide, rfl⟩
  · exact ⟨12, 3, by decide, rfl⟩
  · exact ⟨0, 4, by decide, rfl⟩
  · exact ⟨4, 4, by decide, rfl⟩
  · exact ⟨5, 4, by decide, rfl⟩
  · exact ⟨7, 4, by decide, rfl⟩
  · exact ⟨3, 7, by decide, rfl⟩
  · exact ⟨7, 7, by decide, rfl⟩
  · exact ⟨8, 7, by decide, rfl⟩
  · exact ⟨10, 7, by decide, rfl⟩
  · exact ⟨4, 8, by decide, rfl⟩
  · exact ⟨8, 8, by decide, rfl⟩
  · exact ⟨9, 8, by decide, rfl⟩
  · exact ⟨11, 8, by decide, rfl⟩
  · exact ⟨5, 9, by decide, rfl⟩
  · exact ⟨9, 9, by decide, rfl⟩
  · exact ⟨10, 9, by decide, rfl⟩
  · exact ⟨12, 9, by decide, rfl⟩
  · exact ⟨0, 10, by decide, rfl⟩
  · exact ⟨6, 10, by decide, rfl⟩
  · exact ⟨10, 10, by decide, rfl⟩
  · exact ⟨11, 10, by decide, rfl⟩

theorem distribute (a b c : Bool) : (a && (b || c)) = ((a && b) || (a && c)) := by
  cases a <;> rfl

theorem distributeRight (a b c : Bool) : ((b || c) && a) = ((b && a) || (c && a)) := by
  cases a <;> cases b <;> cases c <;> rfl

def appendGate (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def v27 (x : Fin 26 → Bool) : Bool := GateOp.eval .or [x 3, x 4]
def v28 (x : Fin 26 → Bool) : Bool := GateOp.eval .or [x 6, x 12]
def v29 (x : Fin 26 → Bool) : Bool := GateOp.eval .or [v27 x, v28 x]
def v30 (x : Fin 26 → Bool) : Bool := GateOp.eval .and [x 16, v29 x]
def v31 (x : Fin 26 → Bool) : Bool := GateOp.eval .or [x 0, x 4]
def v32 (x : Fin 26 → Bool) : Bool := GateOp.eval .or [x 5, x 7]
def v33 (x : Fin 26 → Bool) : Bool := GateOp.eval .or [v31 x, v32 x]
def v34 (x : Fin 26 → Bool) : Bool := GateOp.eval .and [x 17, v33 x]
def v35 (x : Fin 26 → Bool) : Bool := GateOp.eval .or [x 3, x 7]
def v36 (x : Fin 26 → Bool) : Bool := GateOp.eval .or [x 8, x 10]
def v37 (x : Fin 26 → Bool) : Bool := GateOp.eval .or [v35 x, v36 x]
def v38 (x : Fin 26 → Bool) : Bool := GateOp.eval .and [x 20, v37 x]
def v39 (x : Fin 26 → Bool) : Bool := GateOp.eval .or [x 4, x 8]
def v40 (x : Fin 26 → Bool) : Bool := GateOp.eval .or [x 9, x 11]
def v41 (x : Fin 26 → Bool) : Bool := GateOp.eval .or [v39 x, v40 x]
def v42 (x : Fin 26 → Bool) : Bool := GateOp.eval .and [x 21, v41 x]
def v43 (x : Fin 26 → Bool) : Bool := GateOp.eval .or [x 5, x 9]
def v44 (x : Fin 26 → Bool) : Bool := GateOp.eval .or [x 10, x 12]
def v45 (x : Fin 26 → Bool) : Bool := GateOp.eval .or [v43 x, v44 x]
def v46 (x : Fin 26 → Bool) : Bool := GateOp.eval .and [x 22, v45 x]
def v47 (x : Fin 26 → Bool) : Bool := GateOp.eval .or [x 0, x 6]
def v48 (x : Fin 26 → Bool) : Bool := GateOp.eval .or [x 10, x 11]
def v49 (x : Fin 26 → Bool) : Bool := GateOp.eval .or [v47 x, v48 x]
def v50 (x : Fin 26 → Bool) : Bool := GateOp.eval .and [x 23, v49 x]
def v51 (x : Fin 26 → Bool) : Bool := GateOp.eval .or [v30 x, v34 x]
def v52 (x : Fin 26 → Bool) : Bool := GateOp.eval .or [v51 x, v38 x]
def v53 (x : Fin 26 → Bool) : Bool := GateOp.eval .or [v52 x, v42 x]
def v54 (x : Fin 26 → Bool) : Bool := GateOp.eval .or [v53 x, v46 x]
def v55 (x : Fin 26 → Bool) : Bool := GateOp.eval .or [v54 x, v50 x]

def stage0 (x : Fin 26 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2)]
theorem initial (x : Fin 26 → Bool) : List.ofFn x ++ [x 1 || x 2] = stage0 x := by rfl
def stage1 (x : Fin 26 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), v27 x]
theorem step1 (x : Fin 26 → Bool) : appendGate (stage0 x) ⟨.or, [3, 4]⟩ = stage1 x := by rfl
def stage2 (x : Fin 26 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), v27 x, v28 x]
theorem step2 (x : Fin 26 → Bool) : appendGate (stage1 x) ⟨.or, [6, 12]⟩ = stage2 x := by rfl
def stage3 (x : Fin 26 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), v27 x, v28 x, v29 x]
theorem step3 (x : Fin 26 → Bool) : appendGate (stage2 x) ⟨.or, [27, 28]⟩ = stage3 x := by rfl
def stage4 (x : Fin 26 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), v27 x, v28 x, v29 x, v30 x]
theorem step4 (x : Fin 26 → Bool) : appendGate (stage3 x) ⟨.and, [16, 29]⟩ = stage4 x := by rfl
def stage5 (x : Fin 26 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), v27 x, v28 x, v29 x, v30 x, v31 x]
theorem step5 (x : Fin 26 → Bool) : appendGate (stage4 x) ⟨.or, [0, 4]⟩ = stage5 x := by rfl
def stage6 (x : Fin 26 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), v27 x, v28 x, v29 x, v30 x, v31 x, v32 x]
theorem step6 (x : Fin 26 → Bool) : appendGate (stage5 x) ⟨.or, [5, 7]⟩ = stage6 x := by rfl
def stage7 (x : Fin 26 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x]
theorem step7 (x : Fin 26 → Bool) : appendGate (stage6 x) ⟨.or, [31, 32]⟩ = stage7 x := by rfl
def stage8 (x : Fin 26 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x]
theorem step8 (x : Fin 26 → Bool) : appendGate (stage7 x) ⟨.and, [17, 33]⟩ = stage8 x := by rfl
def stage9 (x : Fin 26 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x]
theorem step9 (x : Fin 26 → Bool) : appendGate (stage8 x) ⟨.or, [3, 7]⟩ = stage9 x := by rfl
def stage10 (x : Fin 26 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x]
theorem step10 (x : Fin 26 → Bool) : appendGate (stage9 x) ⟨.or, [8, 10]⟩ = stage10 x := by rfl
def stage11 (x : Fin 26 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x]
theorem step11 (x : Fin 26 → Bool) : appendGate (stage10 x) ⟨.or, [35, 36]⟩ = stage11 x := by rfl
def stage12 (x : Fin 26 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x]
theorem step12 (x : Fin 26 → Bool) : appendGate (stage11 x) ⟨.and, [20, 37]⟩ = stage12 x := by rfl
def stage13 (x : Fin 26 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x]
theorem step13 (x : Fin 26 → Bool) : appendGate (stage12 x) ⟨.or, [4, 8]⟩ = stage13 x := by rfl
def stage14 (x : Fin 26 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x]
theorem step14 (x : Fin 26 → Bool) : appendGate (stage13 x) ⟨.or, [9, 11]⟩ = stage14 x := by rfl
def stage15 (x : Fin 26 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x]
theorem step15 (x : Fin 26 → Bool) : appendGate (stage14 x) ⟨.or, [39, 40]⟩ = stage15 x := by rfl
def stage16 (x : Fin 26 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x]
theorem step16 (x : Fin 26 → Bool) : appendGate (stage15 x) ⟨.and, [21, 41]⟩ = stage16 x := by rfl
def stage17 (x : Fin 26 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x]
theorem step17 (x : Fin 26 → Bool) : appendGate (stage16 x) ⟨.or, [5, 9]⟩ = stage17 x := by rfl
def stage18 (x : Fin 26 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x]
theorem step18 (x : Fin 26 → Bool) : appendGate (stage17 x) ⟨.or, [10, 12]⟩ = stage18 x := by rfl
def stage19 (x : Fin 26 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x]
theorem step19 (x : Fin 26 → Bool) : appendGate (stage18 x) ⟨.or, [43, 44]⟩ = stage19 x := by rfl
def stage20 (x : Fin 26 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x]
theorem step20 (x : Fin 26 → Bool) : appendGate (stage19 x) ⟨.and, [22, 45]⟩ = stage20 x := by rfl
def stage21 (x : Fin 26 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x]
theorem step21 (x : Fin 26 → Bool) : appendGate (stage20 x) ⟨.or, [0, 6]⟩ = stage21 x := by rfl
def stage22 (x : Fin 26 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x]
theorem step22 (x : Fin 26 → Bool) : appendGate (stage21 x) ⟨.or, [10, 11]⟩ = stage22 x := by rfl
def stage23 (x : Fin 26 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x]
theorem step23 (x : Fin 26 → Bool) : appendGate (stage22 x) ⟨.or, [47, 48]⟩ = stage23 x := by rfl
def stage24 (x : Fin 26 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x]
theorem step24 (x : Fin 26 → Bool) : appendGate (stage23 x) ⟨.and, [23, 49]⟩ = stage24 x := by rfl
def stage25 (x : Fin 26 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x]
theorem step25 (x : Fin 26 → Bool) : appendGate (stage24 x) ⟨.or, [30, 34]⟩ = stage25 x := by rfl
def stage26 (x : Fin 26 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x]
theorem step26 (x : Fin 26 → Bool) : appendGate (stage25 x) ⟨.or, [51, 38]⟩ = stage26 x := by rfl
def stage27 (x : Fin 26 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x]
theorem step27 (x : Fin 26 → Bool) : appendGate (stage26 x) ⟨.or, [52, 42]⟩ = stage27 x := by rfl
def stage28 (x : Fin 26 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x]
theorem step28 (x : Fin 26 → Bool) : appendGate (stage27 x) ⟨.or, [53, 46]⟩ = stage28 x := by rfl
def stage29 (x : Fin 26 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x]
theorem step29 (x : Fin 26 → Bool) : appendGate (stage28 x) ⟨.or, [54, 50]⟩ = stage29 x := by rfl

theorem allWires (x : Fin 26 → Bool) :
    witness.wires (List.ofFn x ++ [x 1 || x 2]) = stage29 x := by
  change witness.gates.foldl appendGate (List.ofFn x ++ [x 1 || x 2]) = _
  rw [initial]
  simp only [witness, List.foldl_cons, List.foldl_nil, step1, step2, step3, step4, step5, step6, step7, step8, step9, step10, step11, step12, step13, step14, step15, step16, step17, step18, step19, step20, step21, step22, step23, step24, step25, step26, step27, step28, step29]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 6000000 in
theorem evaluation (x : Fin 26 → Bool) :
    witness.eval (List.ofFn x ++ [x 1 || x 2]) = edges.any (fun uv => x uv.1 && x uv.2) := by
  unfold Circuit.eval
  rw [allWires]
  change v55 x = _
  simp [v27, v28, v29, v30, v31, v32, v33, v34, v35, v36, v37, v38, v39, v40, v41, v42, v43, v44, v45, v46, v47, v48, v49, v50, v51, v52, v53, v54, v55, GateOp.eval, edges,
    distribute, distributeRight, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm, Bool.and_comm]

set_option maxRecDepth 20000 in
theorem half :
    ∃ C : Circuit, C.size ≤ 29 ∧ 27 ≤ C.output ∧ C.output < 27 + C.size ∧
      PEqualNP.TopForm.IsAO2 27 C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧
      ∀ x : Fin 26 → Bool, C.eval (List.ofFn x ++ [x 1 || x 2]) = true ↔
        ∃ p l : Fin 13, graph p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true := by
  have nodup : ∀ g ∈ witness.gates, g.inputs.Nodup := by
    intro g hg
    simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  refine ⟨witness, by decide, by decide, by decide, by decide, nodup, ?_⟩
  intro x
  rw [evaluation, List.any_eq_true]
  constructor
  · rintro ⟨uv, hm, h⟩
    obtain ⟨p, l, hi, eq⟩ := edgesOrigins uv hm
    rw [eq] at h
    have hb : x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true := by simpa using h
    exact ⟨p, l, hi, hb.1, hb.2⟩
  · rintro ⟨p, l, hi, hp, hl⟩
    refine ⟨(Fin.castAdd 13 p, Fin.natAdd 13 l), (edgesExactly p l).mp hi, ?_⟩
    change (x (Fin.castAdd 13 p) && x (Fin.natAdd 13 l)) = true
    rw [hp, hl]
    rfl

end PLane9063

#print axioms PLane9063.half
