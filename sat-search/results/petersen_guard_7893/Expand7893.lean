import PEqualNP.Defs

namespace Expand7893

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
  PEqualNP.MetaComplexity.NestedCover

def step (xs : List Bool) (g : Gate) : List Bool :=
  xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)]

theorem sizeFold (p : List Gate) (xs : List Bool) :
    (p.foldl step xs).length = xs.length + p.length := by
  induction p generalizing xs with
  | nil => simp
  | cons g p ih => simp [List.foldl_cons, ih, step]; omega

theorem getAppend (xs : List Bool) (v : Bool) (i : ℕ) :
    (xs ++ [v]).getD i false = if i = xs.length then v else xs.getD i false := by
  rcases lt_trichotomy i xs.length with h | h | h
  · rw [ite_eq_right (by omega), List.getD_append _ _ _ _ h]
  · subst i
    simp [List.getD_eq_getElem?_getD]
  · rw [ite_eq_right (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem prefixAgree (p : List Gate) (clean : ∀ g ∈ p, 0 ∉ g.inputs)
    (xs ys : List Bool) (length : xs.length = ys.length)
    (same : ∀ i, i ≠ 0 → xs.getD i false = ys.getD i false) :
    ∀ i, i ≠ 0 → (p.foldl step xs).getD i false = (p.foldl step ys).getD i false := by
  induction p generalizing xs ys with
  | nil => exact same
  | cons g p ih =>
    have arguments :
        g.inputs.map (fun i => xs.getD i false) = g.inputs.map (fun i => ys.getD i false) := by
      apply List.map_congr_left
      intro i hi
      exact same i (fun eq => clean g (by simp) (eq ▸ hi))
    simp only [List.foldl_cons]
    apply ih (fun t ht => clean t (by simp [ht])) _ _ (by simp [step,length])
    intro i hi
    simp only [step, getAppend, length, arguments, same i hi]

theorem preserveZero (p : List Gate) (xs : List Bool) (positive : 0 < xs.length) :
    (p.foldl step xs).getD 0 false = xs.getD 0 false := by
  induction p generalizing xs with
  | nil => rfl
  | cons g p ih =>
    simp only [List.foldl_cons]
    rw [ih _ (by simp [step]), step, getAppend, ite_eq_right (by omega)]

def insertWire (w i : ℕ) : ℕ :=
  if i = 0 then w+1 else if i ≤ w then i else i+1

def moveGate (w : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (insertWire w)⟩

theorem suffixEval (p : List Gate) (xs ys : List Bool) (w : ℕ)
    (greater : w < ys.length) (length : xs.length = ys.length + 1)
    (agrees : ∀ i, xs.getD (insertWire w i) false = ys.getD i false) :
    ∀ i, ((p.map (moveGate w)).foldl step xs).getD (insertWire w i) false =
      (p.foldl step ys).getD i false := by
  induction p generalizing xs ys with
  | nil => exact agrees
  | cons g p ih =>
    simp only [List.map_cons, List.foldl_cons]
    apply ih _ _ (by simp [step]; omega) (by simp [step, length])
    intro i
    have isNew : insertWire w i = xs.length ↔ i = ys.length := by
      unfold insertWire
      split <;> (first | omega | (split <;> omega))
    have args :
        (moveGate w g).inputs.map (fun j => xs.getD j false) = g.inputs.map (fun j => ys.getD j false) := by
      simp only [moveGate,List.map_map]
      exact List.map_congr_left (fun j _ => agrees j)
    simp only [step, getAppend, isNew, args, agrees i]
    rfl

def expand (B : Circuit) (w : ℕ) : Circuit :=
  let count := w+1-10
  ⟨B.gates.take count ++ [⟨.or,[0,w]⟩] ++ (B.gates.drop count).map (moveGate w),
    insertWire w B.output⟩

theorem gatePrefixSafe (B : Circuit) (w : ℕ)
    (clean : ∀ j g, 10 + j ≤ w → B.gates[j]? = some g → 0 ∉ g.inputs) :
    ∀ g ∈ B.gates.take (w+1-10), 0 ∉ g.inputs := by
  intro g hg
  obtain ⟨j, hj, eq⟩ := List.getElem_of_mem hg
  have small : j < w+1-10 := by simp only [List.length_take] at hj; omega
  have hB : j < B.gates.length := by simp only [List.length_take] at hj; omega
  apply clean j g (by omega)
  rw [List.getElem?_eq_getElem hB]
  congr
  rw [← eq]
  simp

theorem uniqueZeroReader (B : Circuit) (w : ℕ)
    (clean : ∀ j g, 10 + j ≤ w → B.gates[j]? = some g → 0 ∉ g.inputs) :
    ∃ p q : List Gate,
      (expand B w).gates = p ++ [⟨.or,[0,w]⟩] ++ q ∧
      ∀ g ∈ p ++ q, 0 ∉ g.inputs := by
  refine ⟨B.gates.take (w+1-10), (B.gates.drop (w+1-10)).map (moveGate w), rfl, ?_⟩
  intro g hg
  rcases List.mem_append.mp hg with pre | post
  · exact gatePrefixSafe B w clean g pre
  · obtain ⟨g, _, rfl⟩ := List.mem_map.mp post
    simp only [moveGate, List.mem_map]
    rintro ⟨u, _, impossible⟩
    unfold insertWire at impossible
    split at impossible <;> (first | omega | (split at impossible <;> omega))

theorem expandSize (B : Circuit) (w : ℕ) : (expand B w).size = B.size + 1 := by
  have h := congrArg List.length (List.take_append_drop (w+1-10) B.gates)
  simp only [List.length_append] at h
  change (B.gates.take (w+1-10) ++ ([⟨.or,[0,w]⟩] : List Gate) ++
    (B.gates.drop (w+1-10)).map (moveGate w)).length = B.gates.length + 1
  simp only [List.length_append, List.length_cons,List.length_nil,List.length_map]
  omega

def valid (n : ℕ) (gs : List Gate) : Prop :=
  ∀ j (hj : j < gs.length),
    let g := gs[j]
    (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 ∧ ∀ i ∈ g.inputs, i < n+j

theorem asValid (C : Circuit) (n : ℕ) : valid n C.gates ↔ IsAO2 n C := by
  have atIndex (j : ℕ) (hj : j < C.gates.length) : gateAt C j = C.gates[j] :=
    List.getD_eq_getElem _ _ hj
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
      exact (h j hj).1
    · intro j hj i hi
      exact (h j hj).2.2 i (by simpa [atIndex j hj] using hi)
    · intro g hg
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
      exact (h j hj).2.1
  · intro h j hj
    have mem := List.getElem_mem hj
    exact ⟨h.1 _ mem, h.2.2 _ mem, fun i hi => h.2.1 j hj i (by rwa [atIndex j hj])⟩

theorem validAppend {n : ℕ} {p q : List Gate}
    (vp : valid n p) (vq : valid (n + p.length) q) : valid n (p ++ q) := by
  intro j hj
  by_cases inside : j < p.length
  · simpa only [List.getElem_append_left inside] using vp j inside
  · have after : j - p.length < q.length := by simp only [List.length_append] at hj; omega
    have sum : n + p.length + (j - p.length) = n+j := by omega
    simpa only [List.getElem_append_right (by omega : p.length ≤ j), sum]
      using vq (j - p.length) after

theorem expandLegal (B : Circuit) (w : ℕ) (legal : IsAO2 10 B)
    (lower : 10 ≤ w) (upper : w < 10 + B.size) : IsAO2 10 (expand B w) := by
  let k := w+1-10
  let p := B.gates.take k
  let q := B.gates.drop k
  let middle : List Gate := [⟨.or,[0,w]⟩]
  have total : k ≤ B.gates.length := by
    change w < 10 + B.gates.length at upper
    dsimp [k]
    omega
  have pLen : p.length = k := by simp [p, Nat.min_eq_left total]
  have start : 10+p.length = w+1 := by rw [pLen]; dsimp [k]; omega
  have v := (asValid B 10).mpr legal
  have vp : valid 10 p := by
    intro j hj
    have original : j < B.gates.length := by rw [pLen] at hj; omega
    simpa only [p, List.getElem_take] using v j original
  have vm : valid (10+p.length) middle := by
    intro j hj
    have eq : j = 0 := by simpa [middle] using hj
    subst j
    refine ⟨Or.inr rfl, rfl, ?_⟩
    intro i hi
    change i ∈ [0,w] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> omega
  have vq : valid (10 + (p++middle).length) (q.map (moveGate w)) := by
    intro j hj
    have original : k+j < B.gates.length := by
      simp only [q, List.length_map, List.length_drop] at hj
      omega
    have base := v (k+j) original
    simp only [List.getElem_map, q, List.getElem_drop, List.length_append, moveGate]
    refine ⟨base.1, by simpa only [List.length_map] using base.2.1, ?_⟩
    intro out member
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp member
    have before := base.2.2 i hi
    have bound : 10 + (p.length + middle.length) + j = w+2+j := by
      simp [middle]
      omega
    rw [bound]
    have shift : 10+k = w+1 := by omega
    unfold insertWire
    split <;> (first | omega | (split <;> omega))
  exact (asValid (expand B w) 10).mp (validAppend (validAppend vp vm) vq)

theorem expandEval (B : Circuit) (w : ℕ) (lower : 10 ≤ w)
    (upper : w < 10 + B.size)
    (clean : ∀ j g, 10 + j ≤ w → B.gates[j]? = some g → 0 ∉ g.inputs)
    (x : Fin 10 → Bool) :
    (expand B w).eval (List.ofFn x) =
      circuitFun 10 B (Function.update x 0
        (x 0 || (B.wires (List.ofFn (Function.update x 0 false))).getD w false)) := by
  let k := w+1-10
  let p := B.gates.take k
  let q := B.gates.drop k
  have group : p ++ q = B.gates := List.take_append_drop _ _
  have plen : p.length = k := by
    change w < 10 + B.gates.length at upper
    simp [p, List.length_take, Nat.min_eq_left (by dsimp [k]; omega : k ≤ B.gates.length)]
  have pSafe : ∀ g ∈ p, 0 ∉ g.inputs := gatePrefixSafe B w clean
  let xs := List.ofFn x
  let xs0 := List.ofFn (Function.update x 0 false)
  let h := (B.wires xs0).getD w false
  let y := Function.update x 0 (x 0 || h)
  let ys := List.ofFn y
  have xlen : xs.length = 10 := by simp [xs]
  have flen : xs0.length = 10 := by simp [xs0]
  have ylen : ys.length = 10 := by simp [ys]
  have preLength : ∀ b : List Bool, b.length = 10 → (p.foldl step b).length = w+1 := by
    intro b length
    rw [sizeFold, length, plen]
    dsimp [k]
    omega
  have agreePins (i : ℕ) (hi : i ≠ 0) (v : Bool) :
      xs.getD i false = (List.ofFn (Function.update x 0 v)).getD i false := by
    by_cases bound : i < 10
    · change (List.ofFn x).getD i false = (List.ofFn (Function.update x 0 v)).getD i false
      rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using bound),
        List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using bound)]
      simp only [List.getElem_ofFn]
      rw [Function.update_of_ne (by intro eq; exact hi (congrArg Fin.val eq))]
    · change (List.ofFn x).getD i false = (List.ofFn (Function.update x 0 v)).getD i false
      rw [List.getD_eq_default _ _ (by simpa only [List.length_ofFn] using Nat.le_of_not_lt bound),
        List.getD_eq_default _ _ (by simpa only [List.length_ofFn] using Nat.le_of_not_lt bound)]
  have guardPrefix : (p.foldl step xs0).getD w false = h := by
    dsimp [h, Circuit.wires]
    rw [← group, List.foldl_append]
    have preserve : ∀ (gs : List Gate) (a : List Bool), w < a.length →
        (gs.foldl step a).getD w false = a.getD w false := by
      intro gs
      induction gs with
      | nil => simp
      | cons g gs ih =>
        intro a hw
        rw [List.foldl_cons, ih _ (by simp [step]; omega), step, getAppend, ite_eq_right (by omega)]
    exact (preserve q _ (by rw [preLength _ flen]; omega)).symm
  have xv : (p.foldl step xs).getD w false = h :=
    (prefixAgree p pSafe xs xs0 (xlen.trans flen.symm)
      (fun i hi => agreePins i hi false) w (by omega)).trans guardPrefix
  have xzero : (p.foldl step xs).getD 0 false = x 0 := by
    rw [preserveZero _ _ (by rw [xlen]; decide)]
    simp [xs]
  have yzero : (p.foldl step ys).getD 0 false = (x 0 || h) := by
    rw [preserveZero _ _ (by rw [ylen]; decide)]
    simp [ys,y]
  let base := p.foldl step xs ++ [x 0 || h]
  have rel : ∀ i, base.getD (insertWire w i) false = (p.foldl step ys).getD i false := by
    intro i
    by_cases eq : i = 0
    · subst i
      change (p.foldl step xs ++ [x 0 || h]).getD (insertWire w 0) false = _
      rw [insertWire, ite_eq_left rfl, getAppend, preLength _ xlen, ite_eq_left rfl, yzero]
    have same := prefixAgree p pSafe xs ys (xlen.trans ylen.symm)
      (fun i hi => agreePins i hi (x 0 || h)) i eq
    by_cases inside : i ≤ w
    · change (p.foldl step xs ++ [x 0 || h]).getD (insertWire w i) false = _
      rw [insertWire, ite_eq_right eq, ite_eq_left inside, getAppend,
        preLength _ xlen, ite_eq_right (show i ≠ w+1 by omega)]
      exact same
    · have bad : w+1 ≤ i := by omega
      have bad' : base.length ≤ i+1 := by simp [base, preLength _ xlen]; omega
      rw [insertWire, ite_eq_right eq, ite_eq_right inside, List.getD_eq_default _ _ bad',
        List.getD_eq_default _ _ (by rw [preLength _ ylen]; exact bad)]
  have sim := suffixEval q base (p.foldl step ys) w
    (by rw [preLength _ ylen]; omega) (by simp [base, preLength _ xlen, preLength _ ylen]) rel B.output
  have insertStep : step (p.foldl step xs) (⟨.or,[0,w]⟩ : Gate) = base := by
    simp only [step, base, List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
      id_eq, Bool.or_false, xzero, xv]
  change ((((p ++ ([⟨.or,[0,w]⟩] : List Gate)) ++ q.map (moveGate w)).foldl step xs).getD
    (insertWire w B.output) false) = (B.gates.foldl step ys).getD B.output false
  rw [← group]
  simpa only [List.foldl_append, List.foldl_cons, List.foldl_nil, insertStep] using sim

theorem expandPrimary (B : Circuit) (w : ℕ) (legal : IsAO2 10 B)
    (nonzero : w ≠ 0) (upper : w < 10) :
    ∃ E : Circuit, IsAO2 10 E ∧ E.size ≤ B.size + 1 ∧ ∀ x : Fin 10 → Bool,
      circuitFun 10 E x = circuitFun 10 B (Function.update x 0
        (x 0 || (B.wires (List.ofFn (Function.update x 0 false))).getD w false)) := by
  let middle : List Gate := [⟨.or,[0,w]⟩]
  let E : Circuit := ⟨middle ++ B.gates.map (moveGate 9), insertWire 9 B.output⟩
  have firstLegal : valid 10 middle := by
    intro j hj
    have zero : j = 0 := by simpa [middle] using hj
    subst j
    refine ⟨Or.inr rfl, rfl, ?_⟩
    intro i hi
    change i ∈ [0,w] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> omega
  have suffix : valid (10+middle.length) (B.gates.map (moveGate 9)) := by
    intro j hj
    have hh : j < B.gates.length := by simpa only [List.length_map] using hj
    have b := (asValid B 10).mpr legal j hh
    simp only [List.getElem_map, moveGate]
    refine ⟨b.1, by simpa only [List.length_map] using b.2.1, ?_⟩
    intro i hi
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hi
    have before := b.2.2 r hr
    simp only [middle, List.length_cons, List.length_nil]
    unfold insertWire
    split <;> (first | omega | (split <;> omega))
  refine ⟨E, (asValid E 10).mp (validAppend firstLegal suffix), ?_, ?_⟩
  · change (middle ++ B.gates.map _).length ≤ B.gates.length + 1
    simp [middle]
  intro x
  let v : Fin 10 := ⟨w, upper⟩
  have vne : v ≠ 0 := by intro eq; exact nonzero (congrArg Fin.val eq)
  let xfalse := List.ofFn (Function.update x 0 false)
  have hw : xfalse.getD w false = x v := by
    change (List.ofFn (Function.update x 0 false)).getD w false = x v
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using upper)]
    simp only [List.getElem_ofFn, v, Function.update_of_ne vne]
  have preserve : ∀ (gs : List Gate) (s : List Bool), w < s.length →
      (gs.foldl step s).getD w false = s.getD w false := by
    intro gs
    induction gs with
    | nil => simp
    | cons g gs ih =>
      intro s hs
      rw [List.foldl_cons, ih _ (by simp [step]; omega), step, getAppend, ite_eq_right (by omega)]
  have guard : (B.wires xfalse).getD w false = x v :=
    (preserve B.gates xfalse (by simpa [xfalse] using upper)).trans hw
  let xraised := Function.update x 0 (x 0 || x v)
  let xs := List.ofFn x ++ [x 0 || x v]
  let ys := List.ofFn xraised
  have simInputs : ∀ i, xs.getD (insertWire 9 i) false = ys.getD i false := by
    intro i
    by_cases zero : i = 0
    · subst i
      have len : (List.ofFn x).length = 10 := by simp
      change (List.ofFn x ++ [x 0 || x v]).getD (insertWire 9 0) false = _
      rw [insertWire, ite_eq_left rfl, getAppend, len, ite_eq_left rfl]
      simp [ys,xraised]
    by_cases small : i < 10
    · have ne9 : i ≤ 9 := by omega
      have finne : (⟨i, small⟩ : Fin 10) ≠ 0 := by intro eq; exact zero (congrArg Fin.val eq)
      change (List.ofFn x ++ [x 0 || x v]).getD (insertWire 9 i) false =
        (List.ofFn xraised).getD i false
      rw [insertWire, ite_eq_right zero, ite_eq_left ne9,
        List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using small),
        List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using small),
        List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using small)]
      simp only [List.getElem_ofFn, xraised, Function.update_of_ne finne]
    · have high : ¬ i ≤ 9 := by omega
      rw [insertWire, ite_eq_right zero, ite_eq_right high,
        List.getD_eq_default _ _ (by simp [xs]; omega : xs.length ≤ i+1),
        List.getD_eq_default _ _ (by simp [ys]; omega : ys.length ≤ i)]
  have initial : step (List.ofFn x) (⟨.or,[0,w]⟩ : Gate) = xs := by
    have val : (List.ofFn x).getD w false = x v := by
      rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using upper)]
      simp only [List.getElem_ofFn, v]
    have val0 : (List.ofFn x).getD 0 false = x 0 := by simp
    simp only [step, xs, List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
      id_eq, Bool.or_false, val, val0]
  have result := suffixEval B.gates xs ys 9 (by simp [ys])
    (by simp [xs,ys]) simInputs B.output
  change (((middle ++ B.gates.map (moveGate 9)).foldl step (List.ofFn x)).getD
      (insertWire 9 B.output) false) =
    (B.gates.foldl step (List.ofFn (Function.update x 0 (x 0 || (B.wires xfalse).getD w false)))).getD
      B.output false
  rw [guard]
  simpa only [middle, List.foldl_append, List.foldl_cons, List.foldl_nil, initial] using result

theorem substituteOne (B : Circuit) (w : ℕ) (legal : IsAO2 10 B)
    (nonzero : w ≠ 0) (upper : w < 10 + B.size)
    (clean : ∀ j g, 10 + j ≤ w → B.gates[j]? = some g → 0 ∉ g.inputs) :
    ∃ E : Circuit, IsAO2 10 E ∧ E.size ≤ B.size + 1 ∧ ∀ x : Fin 10 → Bool,
      circuitFun 10 E x = circuitFun 10 B (Function.update x 0
        (x 0 || (B.wires (List.ofFn (Function.update x 0 false))).getD w false)) := by
  by_cases lower : 10 ≤ w
  · exact ⟨expand B w, expandLegal B w legal lower upper, (expandSize B w).le,
      expandEval B w lower upper clean⟩
  · exact expandPrimary B w legal nonzero (by omega)

end Expand7893

#print axioms Expand7893.expandSize
#print axioms Expand7893.expandEval
#print axioms Expand7893.uniqueZeroReader
#print axioms Expand7893.expandLegal
#print axioms Expand7893.substituteOne
