import Mathlib
import PEqualNP.Defs

namespace Near9791

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edges : List (ℕ × ℕ) := [(2, 13), (3, 13), (5, 13), (11, 13), (3, 14), (4, 14), (6, 14), (12, 14), (0, 15), (4, 15), (5, 15), (7, 15), (1, 16), (5, 16), (6, 16), (8, 16), (2, 17), (6, 17), (7, 17), (9, 17), (3, 18), (7, 18), (8, 18), (10, 18), (4, 19), (8, 19), (9, 19), (11, 19), (5, 20), (9, 20), (10, 20), (12, 20), (0, 21), (6, 21), (10, 21), (11, 21), (1, 22), (7, 22), (11, 22), (12, 22), (0, 23), (2, 23), (8, 23), (12, 23)]

def witness : Circuit :=
  ⟨[⟨.or, [2,3]⟩,
    ⟨.or, [5,11]⟩,
    ⟨.or, [24,25]⟩,
    ⟨.and, [26,13]⟩,
    ⟨.or, [3,4]⟩,
    ⟨.or, [6,12]⟩,
    ⟨.or, [28,29]⟩,
    ⟨.and, [30,14]⟩,
    ⟨.or, [0,4]⟩,
    ⟨.or, [5,7]⟩,
    ⟨.or, [32,33]⟩,
    ⟨.and, [34,15]⟩,
    ⟨.or, [1,5]⟩,
    ⟨.or, [6,8]⟩,
    ⟨.or, [36,37]⟩,
    ⟨.and, [38,16]⟩,
    ⟨.or, [2,6]⟩,
    ⟨.or, [7,9]⟩,
    ⟨.or, [40,41]⟩,
    ⟨.and, [42,17]⟩,
    ⟨.or, [3,7]⟩,
    ⟨.or, [8,10]⟩,
    ⟨.or, [44,45]⟩,
    ⟨.and, [46,18]⟩,
    ⟨.or, [4,8]⟩,
    ⟨.or, [9,11]⟩,
    ⟨.or, [48,49]⟩,
    ⟨.and, [50,19]⟩,
    ⟨.or, [5,9]⟩,
    ⟨.or, [10,12]⟩,
    ⟨.or, [52,53]⟩,
    ⟨.and, [54,20]⟩,
    ⟨.or, [0,6]⟩,
    ⟨.or, [10,11]⟩,
    ⟨.or, [56,57]⟩,
    ⟨.and, [58,21]⟩,
    ⟨.or, [1,7]⟩,
    ⟨.or, [11,12]⟩,
    ⟨.or, [60,61]⟩,
    ⟨.and, [62,22]⟩,
    ⟨.or, [0,2]⟩,
    ⟨.or, [8,12]⟩,
    ⟨.or, [64,65]⟩,
    ⟨.and, [66,23]⟩,
    ⟨.or, [27,31]⟩,
    ⟨.or, [68,35]⟩,
    ⟨.or, [69,39]⟩,
    ⟨.or, [70,43]⟩,
    ⟨.or, [71,47]⟩,
    ⟨.or, [72,51]⟩,
    ⟨.or, [73,55]⟩,
    ⟨.or, [74,59]⟩,
    ⟨.or, [75,63]⟩,
    ⟨.or, [76,67]⟩], 77⟩

def v24 (x : Fin 24 → Bool) := GateOp.eval .or [x 2, x 3]
def v25 (x : Fin 24 → Bool) := GateOp.eval .or [x 5, x 11]
def v26 (x : Fin 24 → Bool) := GateOp.eval .or [v24 x, v25 x]
def v27 (x : Fin 24 → Bool) := GateOp.eval .and [v26 x, x 13]
def v28 (x : Fin 24 → Bool) := GateOp.eval .or [x 3, x 4]
def v29 (x : Fin 24 → Bool) := GateOp.eval .or [x 6, x 12]
def v30 (x : Fin 24 → Bool) := GateOp.eval .or [v28 x, v29 x]
def v31 (x : Fin 24 → Bool) := GateOp.eval .and [v30 x, x 14]
def v32 (x : Fin 24 → Bool) := GateOp.eval .or [x 0, x 4]
def v33 (x : Fin 24 → Bool) := GateOp.eval .or [x 5, x 7]
def v34 (x : Fin 24 → Bool) := GateOp.eval .or [v32 x, v33 x]
def v35 (x : Fin 24 → Bool) := GateOp.eval .and [v34 x, x 15]
def v36 (x : Fin 24 → Bool) := GateOp.eval .or [x 1, x 5]
def v37 (x : Fin 24 → Bool) := GateOp.eval .or [x 6, x 8]
def v38 (x : Fin 24 → Bool) := GateOp.eval .or [v36 x, v37 x]
def v39 (x : Fin 24 → Bool) := GateOp.eval .and [v38 x, x 16]
def v40 (x : Fin 24 → Bool) := GateOp.eval .or [x 2, x 6]
def v41 (x : Fin 24 → Bool) := GateOp.eval .or [x 7, x 9]
def v42 (x : Fin 24 → Bool) := GateOp.eval .or [v40 x, v41 x]
def v43 (x : Fin 24 → Bool) := GateOp.eval .and [v42 x, x 17]
def v44 (x : Fin 24 → Bool) := GateOp.eval .or [x 3, x 7]
def v45 (x : Fin 24 → Bool) := GateOp.eval .or [x 8, x 10]
def v46 (x : Fin 24 → Bool) := GateOp.eval .or [v44 x, v45 x]
def v47 (x : Fin 24 → Bool) := GateOp.eval .and [v46 x, x 18]
def v48 (x : Fin 24 → Bool) := GateOp.eval .or [x 4, x 8]
def v49 (x : Fin 24 → Bool) := GateOp.eval .or [x 9, x 11]
def v50 (x : Fin 24 → Bool) := GateOp.eval .or [v48 x, v49 x]
def v51 (x : Fin 24 → Bool) := GateOp.eval .and [v50 x, x 19]
def v52 (x : Fin 24 → Bool) := GateOp.eval .or [x 5, x 9]
def v53 (x : Fin 24 → Bool) := GateOp.eval .or [x 10, x 12]
def v54 (x : Fin 24 → Bool) := GateOp.eval .or [v52 x, v53 x]
def v55 (x : Fin 24 → Bool) := GateOp.eval .and [v54 x, x 20]
def v56 (x : Fin 24 → Bool) := GateOp.eval .or [x 0, x 6]
def v57 (x : Fin 24 → Bool) := GateOp.eval .or [x 10, x 11]
def v58 (x : Fin 24 → Bool) := GateOp.eval .or [v56 x, v57 x]
def v59 (x : Fin 24 → Bool) := GateOp.eval .and [v58 x, x 21]
def v60 (x : Fin 24 → Bool) := GateOp.eval .or [x 1, x 7]
def v61 (x : Fin 24 → Bool) := GateOp.eval .or [x 11, x 12]
def v62 (x : Fin 24 → Bool) := GateOp.eval .or [v60 x, v61 x]
def v63 (x : Fin 24 → Bool) := GateOp.eval .and [v62 x, x 22]
def v64 (x : Fin 24 → Bool) := GateOp.eval .or [x 0, x 2]
def v65 (x : Fin 24 → Bool) := GateOp.eval .or [x 8, x 12]
def v66 (x : Fin 24 → Bool) := GateOp.eval .or [v64 x, v65 x]
def v67 (x : Fin 24 → Bool) := GateOp.eval .and [v66 x, x 23]
def v68 (x : Fin 24 → Bool) := GateOp.eval .or [v27 x, v31 x]
def v69 (x : Fin 24 → Bool) := GateOp.eval .or [v68 x, v35 x]
def v70 (x : Fin 24 → Bool) := GateOp.eval .or [v69 x, v39 x]
def v71 (x : Fin 24 → Bool) := GateOp.eval .or [v70 x, v43 x]
def v72 (x : Fin 24 → Bool) := GateOp.eval .or [v71 x, v47 x]
def v73 (x : Fin 24 → Bool) := GateOp.eval .or [v72 x, v51 x]
def v74 (x : Fin 24 → Bool) := GateOp.eval .or [v73 x, v55 x]
def v75 (x : Fin 24 → Bool) := GateOp.eval .or [v74 x, v59 x]
def v76 (x : Fin 24 → Bool) := GateOp.eval .or [v75 x, v63 x]
def v77 (x : Fin 24 → Bool) := GateOp.eval .or [v76 x, v67 x]

def step (xs : List Bool) (g : Gate) : List Bool :=
  xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)]

def ws0 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23]
theorem init (x : Fin 24 → Bool) : List.ofFn x = ws0 x := by rfl
def ws1 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x]
theorem stage1 (x : Fin 24 → Bool) : step (ws0 x) ⟨.or, [2, 3]⟩ = ws1 x := by rfl
def ws2 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x]
theorem stage2 (x : Fin 24 → Bool) : step (ws1 x) ⟨.or, [5, 11]⟩ = ws2 x := by rfl
def ws3 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x]
theorem stage3 (x : Fin 24 → Bool) : step (ws2 x) ⟨.or, [24, 25]⟩ = ws3 x := by rfl
def ws4 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x]
theorem stage4 (x : Fin 24 → Bool) : step (ws3 x) ⟨.and, [26, 13]⟩ = ws4 x := by rfl
def ws5 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x]
theorem stage5 (x : Fin 24 → Bool) : step (ws4 x) ⟨.or, [3, 4]⟩ = ws5 x := by rfl
def ws6 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x]
theorem stage6 (x : Fin 24 → Bool) : step (ws5 x) ⟨.or, [6, 12]⟩ = ws6 x := by rfl
def ws7 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x]
theorem stage7 (x : Fin 24 → Bool) : step (ws6 x) ⟨.or, [28, 29]⟩ = ws7 x := by rfl
def ws8 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x]
theorem stage8 (x : Fin 24 → Bool) : step (ws7 x) ⟨.and, [30, 14]⟩ = ws8 x := by rfl
def ws9 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x]
theorem stage9 (x : Fin 24 → Bool) : step (ws8 x) ⟨.or, [0, 4]⟩ = ws9 x := by rfl
def ws10 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x]
theorem stage10 (x : Fin 24 → Bool) : step (ws9 x) ⟨.or, [5, 7]⟩ = ws10 x := by rfl
def ws11 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x]
theorem stage11 (x : Fin 24 → Bool) : step (ws10 x) ⟨.or, [32, 33]⟩ = ws11 x := by rfl
def ws12 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x]
theorem stage12 (x : Fin 24 → Bool) : step (ws11 x) ⟨.and, [34, 15]⟩ = ws12 x := by rfl
def ws13 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x]
theorem stage13 (x : Fin 24 → Bool) : step (ws12 x) ⟨.or, [1, 5]⟩ = ws13 x := by rfl
def ws14 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x]
theorem stage14 (x : Fin 24 → Bool) : step (ws13 x) ⟨.or, [6, 8]⟩ = ws14 x := by rfl
def ws15 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x]
theorem stage15 (x : Fin 24 → Bool) : step (ws14 x) ⟨.or, [36, 37]⟩ = ws15 x := by rfl
def ws16 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x]
theorem stage16 (x : Fin 24 → Bool) : step (ws15 x) ⟨.and, [38, 16]⟩ = ws16 x := by rfl
def ws17 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x]
theorem stage17 (x : Fin 24 → Bool) : step (ws16 x) ⟨.or, [2, 6]⟩ = ws17 x := by rfl
def ws18 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x]
theorem stage18 (x : Fin 24 → Bool) : step (ws17 x) ⟨.or, [7, 9]⟩ = ws18 x := by rfl
def ws19 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x]
theorem stage19 (x : Fin 24 → Bool) : step (ws18 x) ⟨.or, [40, 41]⟩ = ws19 x := by rfl
def ws20 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x]
theorem stage20 (x : Fin 24 → Bool) : step (ws19 x) ⟨.and, [42, 17]⟩ = ws20 x := by rfl
def ws21 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x]
theorem stage21 (x : Fin 24 → Bool) : step (ws20 x) ⟨.or, [3, 7]⟩ = ws21 x := by rfl
def ws22 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x]
theorem stage22 (x : Fin 24 → Bool) : step (ws21 x) ⟨.or, [8, 10]⟩ = ws22 x := by rfl
def ws23 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x]
theorem stage23 (x : Fin 24 → Bool) : step (ws22 x) ⟨.or, [44, 45]⟩ = ws23 x := by rfl
def ws24 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x]
theorem stage24 (x : Fin 24 → Bool) : step (ws23 x) ⟨.and, [46, 18]⟩ = ws24 x := by rfl
def ws25 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x]
theorem stage25 (x : Fin 24 → Bool) : step (ws24 x) ⟨.or, [4, 8]⟩ = ws25 x := by rfl
def ws26 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x]
theorem stage26 (x : Fin 24 → Bool) : step (ws25 x) ⟨.or, [9, 11]⟩ = ws26 x := by rfl
def ws27 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x]
theorem stage27 (x : Fin 24 → Bool) : step (ws26 x) ⟨.or, [48, 49]⟩ = ws27 x := by rfl
def ws28 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x]
theorem stage28 (x : Fin 24 → Bool) : step (ws27 x) ⟨.and, [50, 19]⟩ = ws28 x := by rfl
def ws29 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x]
theorem stage29 (x : Fin 24 → Bool) : step (ws28 x) ⟨.or, [5, 9]⟩ = ws29 x := by rfl
def ws30 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x]
theorem stage30 (x : Fin 24 → Bool) : step (ws29 x) ⟨.or, [10, 12]⟩ = ws30 x := by rfl
def ws31 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x]
theorem stage31 (x : Fin 24 → Bool) : step (ws30 x) ⟨.or, [52, 53]⟩ = ws31 x := by rfl
def ws32 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x]
theorem stage32 (x : Fin 24 → Bool) : step (ws31 x) ⟨.and, [54, 20]⟩ = ws32 x := by rfl
def ws33 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x]
theorem stage33 (x : Fin 24 → Bool) : step (ws32 x) ⟨.or, [0, 6]⟩ = ws33 x := by rfl
def ws34 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x]
theorem stage34 (x : Fin 24 → Bool) : step (ws33 x) ⟨.or, [10, 11]⟩ = ws34 x := by rfl
def ws35 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x]
theorem stage35 (x : Fin 24 → Bool) : step (ws34 x) ⟨.or, [56, 57]⟩ = ws35 x := by rfl
def ws36 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x]
theorem stage36 (x : Fin 24 → Bool) : step (ws35 x) ⟨.and, [58, 21]⟩ = ws36 x := by rfl
def ws37 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x]
theorem stage37 (x : Fin 24 → Bool) : step (ws36 x) ⟨.or, [1, 7]⟩ = ws37 x := by rfl
def ws38 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x]
theorem stage38 (x : Fin 24 → Bool) : step (ws37 x) ⟨.or, [11, 12]⟩ = ws38 x := by rfl
def ws39 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x]
theorem stage39 (x : Fin 24 → Bool) : step (ws38 x) ⟨.or, [60, 61]⟩ = ws39 x := by rfl
def ws40 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x]
theorem stage40 (x : Fin 24 → Bool) : step (ws39 x) ⟨.and, [62, 22]⟩ = ws40 x := by rfl
def ws41 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x]
theorem stage41 (x : Fin 24 → Bool) : step (ws40 x) ⟨.or, [0, 2]⟩ = ws41 x := by rfl
def ws42 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x, v65 x]
theorem stage42 (x : Fin 24 → Bool) : step (ws41 x) ⟨.or, [8, 12]⟩ = ws42 x := by rfl
def ws43 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x, v65 x, v66 x]
theorem stage43 (x : Fin 24 → Bool) : step (ws42 x) ⟨.or, [64, 65]⟩ = ws43 x := by rfl
def ws44 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x, v65 x, v66 x, v67 x]
theorem stage44 (x : Fin 24 → Bool) : step (ws43 x) ⟨.and, [66, 23]⟩ = ws44 x := by rfl
def ws45 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x, v65 x, v66 x, v67 x, v68 x]
theorem stage45 (x : Fin 24 → Bool) : step (ws44 x) ⟨.or, [27, 31]⟩ = ws45 x := by rfl
def ws46 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x, v65 x, v66 x, v67 x, v68 x, v69 x]
theorem stage46 (x : Fin 24 → Bool) : step (ws45 x) ⟨.or, [68, 35]⟩ = ws46 x := by rfl
def ws47 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x, v65 x, v66 x, v67 x, v68 x, v69 x, v70 x]
theorem stage47 (x : Fin 24 → Bool) : step (ws46 x) ⟨.or, [69, 39]⟩ = ws47 x := by rfl
def ws48 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x, v65 x, v66 x, v67 x, v68 x, v69 x, v70 x, v71 x]
theorem stage48 (x : Fin 24 → Bool) : step (ws47 x) ⟨.or, [70, 43]⟩ = ws48 x := by rfl
def ws49 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x, v65 x, v66 x, v67 x, v68 x, v69 x, v70 x, v71 x, v72 x]
theorem stage49 (x : Fin 24 → Bool) : step (ws48 x) ⟨.or, [71, 47]⟩ = ws49 x := by rfl
def ws50 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x, v65 x, v66 x, v67 x, v68 x, v69 x, v70 x, v71 x, v72 x, v73 x]
theorem stage50 (x : Fin 24 → Bool) : step (ws49 x) ⟨.or, [72, 51]⟩ = ws50 x := by rfl
def ws51 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x, v65 x, v66 x, v67 x, v68 x, v69 x, v70 x, v71 x, v72 x, v73 x, v74 x]
theorem stage51 (x : Fin 24 → Bool) : step (ws50 x) ⟨.or, [73, 55]⟩ = ws51 x := by rfl
def ws52 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x, v65 x, v66 x, v67 x, v68 x, v69 x, v70 x, v71 x, v72 x, v73 x, v74 x, v75 x]
theorem stage52 (x : Fin 24 → Bool) : step (ws51 x) ⟨.or, [74, 59]⟩ = ws52 x := by rfl
def ws53 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x, v65 x, v66 x, v67 x, v68 x, v69 x, v70 x, v71 x, v72 x, v73 x, v74 x, v75 x, v76 x]
theorem stage53 (x : Fin 24 → Bool) : step (ws52 x) ⟨.or, [75, 63]⟩ = ws53 x := by rfl
def ws54 (x : Fin 24 → Bool) : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x, v65 x, v66 x, v67 x, v68 x, v69 x, v70 x, v71 x, v72 x, v73 x, v74 x, v75 x, v76 x, v77 x]
theorem stage54 (x : Fin 24 → Bool) : step (ws53 x) ⟨.or, [76, 67]⟩ = ws54 x := by rfl

theorem orDistrib (a b c : Bool) : ((a || b) && c) = ((a && c) || (b && c)) := by
  cases a <;> cases b <;> cases c <;> rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
theorem eval_star (x : Fin 24 → Bool) :
    witness.eval (List.ofFn x) = v77 x := by
  change ((witness.gates.foldl step (List.ofFn x)).getD 77 false) = _
  rw [init]
  simp only [witness, List.foldl_cons, List.foldl_nil, stage1, stage2, stage3, stage4, stage5, stage6, stage7, stage8, stage9, stage10, stage11, stage12, stage13, stage14, stage15, stage16, stage17, stage18, stage19, stage20, stage21, stage22, stage23, stage24, stage25, stage26, stage27, stage28, stage29, stage30, stage31, stage32, stage33, stage34, stage35, stage36, stage37, stage38, stage39, stage40, stage41, stage42, stage43, stage44, stage45, stage46, stage47, stage48, stage49, stage50, stage51, stage52, stage53, stage54]
  rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
theorem star_edges (x : Fin 24 → Bool) :
    v77 x = edges.any (fun e => x (Fin.ofNat 24 e.1) && x (Fin.ofNat 24 e.2)) := by
  simp [v24, v25, v26, v27, v28, v29, v30, v31, v32, v33, v34, v35, v36, v37, v38, v39, v40, v41, v42, v43, v44, v45, v46, v47, v48, v49, v50, v51, v52, v53, v54, v55, v56, v57, v58, v59, v60, v61, v62, v63, v64, v65, v66, v67, v68, v69, v70, v71, v72, v73, v74, v75, v76, v77, GateOp.eval, edges, orDistrib, Bool.or_assoc]
  rfl

set_option maxRecDepth 20000 in
theorem witness54 :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 54 ∧ ∀ x : Fin 24 → Bool,
      (C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin 24, (u.val, v.val) ∈ edges ∧ x u = true ∧ x v = true) := by
  have monotone : Monotone2 witness := by
    intro g hg
    simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first
      | exact ⟨Or.inl rfl, by decide⟩
      | exact ⟨Or.inr rfl, by decide⟩
  refine ⟨witness, monotone, by decide, ?_⟩
  intro x
  rw [eval_star, star_edges, List.any_eq_true]
  constructor
  · rintro ⟨⟨a, b⟩, h, hval⟩
    have hab : edges.all (fun e => decide (e.1 < 24 ∧ e.2 < 24)) = true := by decide
    obtain ⟨ha, hb⟩ := of_decide_eq_true ((List.all_eq_true.1 hab) (a, b) h)
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, h, by
      simpa [Fin.ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using hval⟩
  · rintro ⟨a, b, h, ha, hb⟩
    exact ⟨(a.val,b.val), h, by simp [ha, hb]⟩

end Near9791
