import Mathlib
import PEqualNP.Defs
import PEqualNP.Defs.BlindGate
import PEqualNP.Defs.TopForm

namespace LMeta4874Audit
open PEqualNP.CircuitLowerBounds

def witness : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.or, [3, 14]⟩, ⟨.and, [7, 15]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [5, 17]⟩, ⟨.and, [9, 18]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [6, 20]⟩, ⟨.and, [10, 21]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [5, 23]⟩, ⟨.and, [11, 24]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [6, 26]⟩, ⟨.and, [12, 27]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [6, 29]⟩, ⟨.and, [13, 30]⟩, ⟨.or, [16, 19]⟩, ⟨.or, [22, 32]⟩, ⟨.or, [25, 33]⟩, ⟨.or, [28, 34]⟩, ⟨.or, [31, 35]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [4, 37]⟩, ⟨.or, [8, 36]⟩, ⟨.or, [36, 38]⟩, ⟨.and, [39, 40]⟩], 41⟩

def incident (p l : Fin 7) : Prop := p = l ∨ p = l + 1 ∨ p = l + 3

instance (p l : Fin 7) : Decidable (incident p l) := inferInstanceAs (Decidable (p = l ∨ p = l + 1 ∨ p = l + 3))

def edges : List (Fin 14 × Fin 14) := [(0, 7), (0, 11), (0, 13), (1, 7), (1, 8), (1, 12), (2, 8), (2, 9), (2, 13), (3, 7), (3, 9), (3, 10), (4, 8), (4, 10), (4, 11), (5, 9), (5, 11), (5, 12), (6, 10), (6, 12), (6, 13)]

theorem edgeIn : ∀ p l : Fin 7, incident p l ↔
    (Fin.castAdd 7 p, Fin.natAdd 7 l) ∈ edges := by
  decide +kernel

theorem edgeSupport (uv : Fin 14 × Fin 14) (h : uv ∈ edges) :
    ∃ p l : Fin 7, incident p l ∧ uv = (Fin.castAdd 7 p, Fin.natAdd 7 l) := by
  simp only [edges, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, 0, by decide +kernel, rfl⟩
  · exact ⟨0, 4, by decide +kernel, rfl⟩
  · exact ⟨0, 6, by decide +kernel, rfl⟩
  · exact ⟨1, 0, by decide +kernel, rfl⟩
  · exact ⟨1, 1, by decide +kernel, rfl⟩
  · exact ⟨1, 5, by decide +kernel, rfl⟩
  · exact ⟨2, 1, by decide +kernel, rfl⟩
  · exact ⟨2, 2, by decide +kernel, rfl⟩
  · exact ⟨2, 6, by decide +kernel, rfl⟩
  · exact ⟨3, 0, by decide +kernel, rfl⟩
  · exact ⟨3, 2, by decide +kernel, rfl⟩
  · exact ⟨3, 3, by decide +kernel, rfl⟩
  · exact ⟨4, 1, by decide +kernel, rfl⟩
  · exact ⟨4, 3, by decide +kernel, rfl⟩
  · exact ⟨4, 4, by decide +kernel, rfl⟩
  · exact ⟨5, 2, by decide +kernel, rfl⟩
  · exact ⟨5, 4, by decide +kernel, rfl⟩
  · exact ⟨5, 5, by decide +kernel, rfl⟩
  · exact ⟨6, 3, by decide +kernel, rfl⟩
  · exact ⟨6, 5, by decide +kernel, rfl⟩
  · exact ⟨6, 6, by decide +kernel, rfl⟩

def appendGate (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def stage0 (x : Fin 14 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13]

theorem initial (x : Fin 14 → Bool) : List.ofFn x = stage0 x := by rfl

def v14 (x : Fin 14 → Bool) : Bool := GateOp.eval .or [x 0, x 1]

def stage1 (x : Fin 14 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, v14 x]

theorem step1 (x : Fin 14 → Bool) : appendGate (stage0 x) ⟨.or, [0, 1]⟩ = stage1 x := by rfl

def v15 (x : Fin 14 → Bool) : Bool := GateOp.eval .or [x 3, v14 x]

def stage2 (x : Fin 14 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, v14 x, v15 x]

theorem step2 (x : Fin 14 → Bool) : appendGate (stage1 x) ⟨.or, [3, 14]⟩ = stage2 x := by rfl

def v16 (x : Fin 14 → Bool) : Bool := GateOp.eval .and [x 7, v15 x]

def stage3 (x : Fin 14 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, v14 x, v15 x, v16 x]

theorem step3 (x : Fin 14 → Bool) : appendGate (stage2 x) ⟨.and, [7, 15]⟩ = stage3 x := by rfl

def v17 (x : Fin 14 → Bool) : Bool := GateOp.eval .or [x 2, x 3]

def stage4 (x : Fin 14 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, v14 x, v15 x, v16 x, v17 x]

theorem step4 (x : Fin 14 → Bool) : appendGate (stage3 x) ⟨.or, [2, 3]⟩ = stage4 x := by rfl

def v18 (x : Fin 14 → Bool) : Bool := GateOp.eval .or [x 5, v17 x]

def stage5 (x : Fin 14 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, v14 x, v15 x, v16 x, v17 x, v18 x]

theorem step5 (x : Fin 14 → Bool) : appendGate (stage4 x) ⟨.or, [5, 17]⟩ = stage5 x := by rfl

def v19 (x : Fin 14 → Bool) : Bool := GateOp.eval .and [x 9, v18 x]

def stage6 (x : Fin 14 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, v14 x, v15 x, v16 x, v17 x, v18 x, v19 x]

theorem step6 (x : Fin 14 → Bool) : appendGate (stage5 x) ⟨.and, [9, 18]⟩ = stage6 x := by rfl

def v20 (x : Fin 14 → Bool) : Bool := GateOp.eval .or [x 3, x 4]

def stage7 (x : Fin 14 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, v14 x, v15 x, v16 x, v17 x, v18 x, v19 x, v20 x]

theorem step7 (x : Fin 14 → Bool) : appendGate (stage6 x) ⟨.or, [3, 4]⟩ = stage7 x := by rfl

def v21 (x : Fin 14 → Bool) : Bool := GateOp.eval .or [x 6, v20 x]

def stage8 (x : Fin 14 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, v14 x, v15 x, v16 x, v17 x, v18 x, v19 x, v20 x, v21 x]

theorem step8 (x : Fin 14 → Bool) : appendGate (stage7 x) ⟨.or, [6, 20]⟩ = stage8 x := by rfl

def v22 (x : Fin 14 → Bool) : Bool := GateOp.eval .and [x 10, v21 x]

def stage9 (x : Fin 14 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, v14 x, v15 x, v16 x, v17 x, v18 x, v19 x, v20 x, v21 x, v22 x]

theorem step9 (x : Fin 14 → Bool) : appendGate (stage8 x) ⟨.and, [10, 21]⟩ = stage9 x := by rfl

def v23 (x : Fin 14 → Bool) : Bool := GateOp.eval .or [x 0, x 4]

def stage10 (x : Fin 14 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, v14 x, v15 x, v16 x, v17 x, v18 x, v19 x, v20 x, v21 x, v22 x, v23 x]

theorem step10 (x : Fin 14 → Bool) : appendGate (stage9 x) ⟨.or, [0, 4]⟩ = stage10 x := by rfl

def v24 (x : Fin 14 → Bool) : Bool := GateOp.eval .or [x 5, v23 x]

def stage11 (x : Fin 14 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, v14 x, v15 x, v16 x, v17 x, v18 x, v19 x, v20 x, v21 x, v22 x, v23 x, v24 x]

theorem step11 (x : Fin 14 → Bool) : appendGate (stage10 x) ⟨.or, [5, 23]⟩ = stage11 x := by rfl

def v25 (x : Fin 14 → Bool) : Bool := GateOp.eval .and [x 11, v24 x]

def stage12 (x : Fin 14 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, v14 x, v15 x, v16 x, v17 x, v18 x, v19 x, v20 x, v21 x, v22 x, v23 x, v24 x, v25 x]

theorem step12 (x : Fin 14 → Bool) : appendGate (stage11 x) ⟨.and, [11, 24]⟩ = stage12 x := by rfl

def v26 (x : Fin 14 → Bool) : Bool := GateOp.eval .or [x 1, x 5]

def stage13 (x : Fin 14 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, v14 x, v15 x, v16 x, v17 x, v18 x, v19 x, v20 x, v21 x, v22 x, v23 x, v24 x, v25 x, v26 x]

theorem step13 (x : Fin 14 → Bool) : appendGate (stage12 x) ⟨.or, [1, 5]⟩ = stage13 x := by rfl

def v27 (x : Fin 14 → Bool) : Bool := GateOp.eval .or [x 6, v26 x]

def stage14 (x : Fin 14 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, v14 x, v15 x, v16 x, v17 x, v18 x, v19 x, v20 x, v21 x, v22 x, v23 x, v24 x, v25 x, v26 x, v27 x]

theorem step14 (x : Fin 14 → Bool) : appendGate (stage13 x) ⟨.or, [6, 26]⟩ = stage14 x := by rfl

def v28 (x : Fin 14 → Bool) : Bool := GateOp.eval .and [x 12, v27 x]

def stage15 (x : Fin 14 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, v14 x, v15 x, v16 x, v17 x, v18 x, v19 x, v20 x, v21 x, v22 x, v23 x, v24 x, v25 x, v26 x, v27 x, v28 x]

theorem step15 (x : Fin 14 → Bool) : appendGate (stage14 x) ⟨.and, [12, 27]⟩ = stage15 x := by rfl

def v29 (x : Fin 14 → Bool) : Bool := GateOp.eval .or [x 0, x 2]

def stage16 (x : Fin 14 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, v14 x, v15 x, v16 x, v17 x, v18 x, v19 x, v20 x, v21 x, v22 x, v23 x, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x]

theorem step16 (x : Fin 14 → Bool) : appendGate (stage15 x) ⟨.or, [0, 2]⟩ = stage16 x := by rfl

def v30 (x : Fin 14 → Bool) : Bool := GateOp.eval .or [x 6, v29 x]

def stage17 (x : Fin 14 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, v14 x, v15 x, v16 x, v17 x, v18 x, v19 x, v20 x, v21 x, v22 x, v23 x, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x]

theorem step17 (x : Fin 14 → Bool) : appendGate (stage16 x) ⟨.or, [6, 29]⟩ = stage17 x := by rfl

def v31 (x : Fin 14 → Bool) : Bool := GateOp.eval .and [x 13, v30 x]

def stage18 (x : Fin 14 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, v14 x, v15 x, v16 x, v17 x, v18 x, v19 x, v20 x, v21 x, v22 x, v23 x, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x]

theorem step18 (x : Fin 14 → Bool) : appendGate (stage17 x) ⟨.and, [13, 30]⟩ = stage18 x := by rfl

def v32 (x : Fin 14 → Bool) : Bool := GateOp.eval .or [v16 x, v19 x]

def stage19 (x : Fin 14 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, v14 x, v15 x, v16 x, v17 x, v18 x, v19 x, v20 x, v21 x, v22 x, v23 x, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x]

theorem step19 (x : Fin 14 → Bool) : appendGate (stage18 x) ⟨.or, [16, 19]⟩ = stage19 x := by rfl

def v33 (x : Fin 14 → Bool) : Bool := GateOp.eval .or [v22 x, v32 x]

def stage20 (x : Fin 14 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, v14 x, v15 x, v16 x, v17 x, v18 x, v19 x, v20 x, v21 x, v22 x, v23 x, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x]

theorem step20 (x : Fin 14 → Bool) : appendGate (stage19 x) ⟨.or, [22, 32]⟩ = stage20 x := by rfl

def v34 (x : Fin 14 → Bool) : Bool := GateOp.eval .or [v25 x, v33 x]

def stage21 (x : Fin 14 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, v14 x, v15 x, v16 x, v17 x, v18 x, v19 x, v20 x, v21 x, v22 x, v23 x, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x]

theorem step21 (x : Fin 14 → Bool) : appendGate (stage20 x) ⟨.or, [25, 33]⟩ = stage21 x := by rfl

def v35 (x : Fin 14 → Bool) : Bool := GateOp.eval .or [v28 x, v34 x]

def stage22 (x : Fin 14 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, v14 x, v15 x, v16 x, v17 x, v18 x, v19 x, v20 x, v21 x, v22 x, v23 x, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x]

theorem step22 (x : Fin 14 → Bool) : appendGate (stage21 x) ⟨.or, [28, 34]⟩ = stage22 x := by rfl

def v36 (x : Fin 14 → Bool) : Bool := GateOp.eval .or [v31 x, v35 x]

def stage23 (x : Fin 14 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, v14 x, v15 x, v16 x, v17 x, v18 x, v19 x, v20 x, v21 x, v22 x, v23 x, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x]

theorem step23 (x : Fin 14 → Bool) : appendGate (stage22 x) ⟨.or, [31, 35]⟩ = stage23 x := by rfl

def v37 (x : Fin 14 → Bool) : Bool := GateOp.eval .or [x 1, x 2]

def stage24 (x : Fin 14 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, v14 x, v15 x, v16 x, v17 x, v18 x, v19 x, v20 x, v21 x, v22 x, v23 x, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x]

theorem step24 (x : Fin 14 → Bool) : appendGate (stage23 x) ⟨.or, [1, 2]⟩ = stage24 x := by rfl

def v38 (x : Fin 14 → Bool) : Bool := GateOp.eval .or [x 4, v37 x]

def stage25 (x : Fin 14 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, v14 x, v15 x, v16 x, v17 x, v18 x, v19 x, v20 x, v21 x, v22 x, v23 x, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x]

theorem step25 (x : Fin 14 → Bool) : appendGate (stage24 x) ⟨.or, [4, 37]⟩ = stage25 x := by rfl

def v39 (x : Fin 14 → Bool) : Bool := GateOp.eval .or [x 8, v36 x]

def stage26 (x : Fin 14 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, v14 x, v15 x, v16 x, v17 x, v18 x, v19 x, v20 x, v21 x, v22 x, v23 x, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x]

theorem step26 (x : Fin 14 → Bool) : appendGate (stage25 x) ⟨.or, [8, 36]⟩ = stage26 x := by rfl

def v40 (x : Fin 14 → Bool) : Bool := GateOp.eval .or [v36 x, v38 x]

def stage27 (x : Fin 14 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, v14 x, v15 x, v16 x, v17 x, v18 x, v19 x, v20 x, v21 x, v22 x, v23 x, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x]

theorem step27 (x : Fin 14 → Bool) : appendGate (stage26 x) ⟨.or, [36, 38]⟩ = stage27 x := by rfl

def v41 (x : Fin 14 → Bool) : Bool := GateOp.eval .and [v39 x, v40 x]

def stage28 (x : Fin 14 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, v14 x, v15 x, v16 x, v17 x, v18 x, v19 x, v20 x, v21 x, v22 x, v23 x, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x]

theorem step28 (x : Fin 14 → Bool) : appendGate (stage27 x) ⟨.and, [39, 40]⟩ = stage28 x := by rfl

theorem allWires (x : Fin 14 → Bool) : witness.wires (List.ofFn x) = stage28 x := by
  change witness.gates.foldl appendGate (List.ofFn x) = stage28 x
  rw [initial]
  simp only [witness, List.foldl_cons, List.foldl_nil, step1, step2, step3, step4, step5, step6, step7, step8, step9, step10, step11, step12, step13, step14, step15, step16, step17, step18, step19, step20, step21, step22, step23, step24, step25, step26, step27, step28]

theorem factor (r a b : Bool) : ((a || r) && (r || b)) = (r || (a && b)) := by
  cases r <;> cases a <;> cases b <;> rfl

theorem distributeRight (x y z : Bool) : ((y || z) && x) = ((y && x) || (z && x)) := by
  cases x <;> cases y <;> cases z <;> rfl

theorem distribute (x y z : Bool) : (x && (y || z)) = ((x && y) || (x && z)) := by
  cases x <;> rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem evalWitness (x : Fin 14 → Bool) :
    witness.eval (List.ofFn x) = edges.any (fun uv => x uv.1 && x uv.2) := by
  unfold Circuit.eval
  rw [allWires]
  change v41 x = _
  simp only [v41, v39, v40, GateOp.eval, List.any_cons, List.all_cons, id_eq, List.any_nil,
    List.all_nil, Bool.and_true, Bool.or_false]
  rw [factor]
  simp [v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33, v34, v35, v36, v37, v38, GateOp.eval, edges, distribute, distributeRight, Bool.or_assoc, Bool.or_left_comm,
    Bool.or_comm, Bool.and_comm]

theorem evalGraph (x : Fin 14 → Bool) : witness.eval (List.ofFn x) = true ↔
    ∃ p l : Fin 7, incident p l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true := by
  rw [evalWitness, List.any_eq_true]
  constructor
  · rintro ⟨uv, hm, h⟩
    obtain ⟨p,l,hi,eq⟩ := edgeSupport uv hm
    rw [eq] at h
    have both : x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true := by simpa using h
    exact ⟨p,l,hi,both.1,both.2⟩
  · rintro ⟨p,l,hp,hx,hy⟩
    refine ⟨(Fin.castAdd 7 p, Fin.natAdd 7 l), (edgeIn p l).mp hp, ?_⟩
    change (x (Fin.castAdd 7 p) && x (Fin.natAdd 7 l)) = true
    rw [hx, hy]
    rfl

theorem basis : PEqualNP.TopForm.IsAO2 14 witness := by
  refine ⟨?_, ?_, ?_⟩
  · intro g h
    simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro j hj i hi
    change j < 28 at hj
    interval_cases j <;> simp [PEqualNP.MetaComplexity.NestedCover.gateAt, witness] at hi <;> omega
  · intro g h
    simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem pins : ∀ g ∈ witness.gates, g.inputs.Nodup := by
  intro g h
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem upper28 : (have x1 : Fin (7 : ℕ) → Fin (7 : ℕ) → Prop := fun (x1 x2 : Fin (7 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (7 : ℕ)) ∨ x1 = x2 + (3 : Fin (7 : ℕ)); have x2 : (Fin (14 : ℕ) → Bool) → Prop := fun (x2 : Fin (14 : ℕ) → Bool) => ∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), x1 x3 x4 ∧ x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true; ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : ℕ) (x6 : ℕ),   x3.size ≤ (28 : ℕ) ∧     PEqualNP.TopForm.IsAO2 (14 : ℕ) x3 ∧       (∀ x7 ∈ x3.gates, x7.inputs.Nodup) ∧         x3.output = (14 : ℕ) + x4 ∧           x3.gates[x4]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x5, x6] : PEqualNP.CircuitLowerBounds.Gate } ∧             (∀ (x7 x8 : Fin (7 : ℕ)), x1 x7 x8 → x3.eval (List.ofFn fun (x10 : Fin (14 : ℕ)) => Decidable.decide (x10 = Fin.castAdd (7 : ℕ) x7 ∨ x10 = Fin.natAdd (7 : ℕ) x8)) = Bool.true) ∧               (∀ (x7 : Fin (14 : ℕ) → Bool), Maximal (fun (x8 : Fin (14 : ℕ) → Bool) => ¬x2 x8) x7 → x3.eval (List.ofFn x7) = Bool.false) ∧                 ∀ x7 ∈ [(0 : Fin (14 : ℕ)), (7 : Fin (14 : ℕ))],                   have x9 : Fin (14 : ℕ) → Bool := fun (x9 : Fin (14 : ℕ)) => Decidable.decide (x9 = x7);                   PEqualNP.BlindGate.wireValue x3 (14 : ℕ) x9 x5 = Bool.false ∧ PEqualNP.BlindGate.wireValue x3 (14 : ℕ) x9 x6 = Bool.false) := by
  dsimp only
  refine ⟨witness, 27, 39, 40, by decide, basis, pins, rfl, rfl, ?_, ?_, ?_⟩
  · intro p l h
    exact (evalGraph _).mpr ⟨p, l, h, by simp, by simp⟩
  · intro x h
    cases hw : witness.eval (List.ofFn x) with
    | false => rfl
    | true => exact (h.prop ((evalGraph x).mp hw)).elim
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> simp only [PEqualNP.BlindGate.wireValue, allWires] <;> decide +kernel

#print axioms upper28
end LMeta4874Audit
