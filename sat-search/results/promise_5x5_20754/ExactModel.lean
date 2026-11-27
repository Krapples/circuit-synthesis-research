import PEqualNP.Defs.Represents
import ActiveBudget

namespace ActiveBudget20754

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

private theorem appendLookup {α : Type} (xs ys : List α) (d : α) (i : ℕ) :
    (xs ++ ys).getD i d =
      if i < xs.length then xs.getD i d else ys.getD (i - xs.length) d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append]
  split <;> rfl

private theorem read_eq (w : List Table) (i : Wire) :
    read w i = w.getD i.toNat 0 := by
  induction w generalizing i with
  | nil => rfl
  | cons v vs ih =>
    by_cases hi : i = 0
    · subst i
      rfl
    · have hpos : 0 < i.toNat := by
        by_contra! h
        exact hi (BitVec.eq_of_toNat_eq (by simpa using h))
      have hsub : (i - 1).toNat = i.toNat - 1 := by
        have hle : (1 : Wire) ≤ i := by
          change 1 ≤ i.toNat
          omega
        exact BitVec.toNat_sub_of_le hle
      cases hn : i.toNat with
      | zero => omega
      | succ n =>
        rw [read, ite_eq_right (fun h => hi (beq_iff_eq.mp h)), ih, hsub, hn,
          List.getD_cons_succ, show n + 1 - 1 = n by omega]

private def row (k : Fin 12) : Fin 5 := ⟨2 + k.val / 4, by omega⟩
private def col (k : Fin 12) : Fin 5 := ⟨k.val % 4, by omega⟩
private def target (u v : Fin 5) : Bool := (12815360 : ℕ).testBit (5 * u.val + v.val)
private def originalInputs : List Table := [0, 0, 15, 240, 3840, 273, 546, 1092, 2184, 0]

private theorem initial_bits (k : Fin 12) :
    originalInputs.map (·.getLsbD k.val) = oneEach (row k) (col k) := by
  revert k
  decide +kernel

private theorem target_bits (k : Fin 12) :
    (3187 : Table).getLsbD k.val = target (row k) (col k) := by
  revert k
  decide +kernel

private def packedIndex (n i : ℕ) : ℕ :=
  if 2 ≤ i ∧ i < 9 then i else if 10 ≤ i ∧ i < 10 + n then i - 1 else 0

private theorem packedIndex_lt (n i : ℕ) (h : n ≤ 7) : packedIndex n i < 16 := by
  unfold packedIndex
  split
  · omega
  · split <;> omega

private theorem map_getD_bit (w : List Table) (i k : ℕ) :
    (w.getD i 0).getLsbD k = (w.map (·.getLsbD k)).getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[i]? <;> simp

private theorem wire_map (ts : List Table) (i : ℕ) (hn : ts.length ≤ 7) :
    read (inputs ++ ts) (BitVec.ofNat 4 (packedIndex ts.length i)) =
      (originalInputs ++ ts).getD i 0 := by
  rw [read_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (packedIndex_lt _ _ hn)]
  rw [appendLookup, appendLookup]
  have hpacked : inputs.length = 9 := rfl
  have horiginal : originalInputs.length = 10 := rfl
  rw [hpacked, horiginal]
  by_cases hi : i < 10
  · have hc : ∀ j : Fin 10,
        inputs.getD (if 2 ≤ j.val ∧ j.val < 9 then j.val else 0) 0 =
          originalInputs.getD j.val 0 := by decide +kernel
    have hj := hc ⟨i, hi⟩
    have hno : ¬ (10 ≤ i ∧ i < 10 + ts.length) := by omega
    have hbefore : (if 2 ≤ i ∧ i < 9 then i else 0) < 9 := by split <;> omega
    simpa [packedIndex, hno, hbefore, hi] using hj
  · by_cases hb : i < 10 + ts.length
    · have hgate : 10 ≤ i ∧ i < 10 + ts.length := ⟨by omega, hb⟩
      have hinactive : ¬ (2 ≤ i ∧ i < 9) := by omega
      have hnotinput : ¬ i - 1 < 9 := by omega
      have hsub : i - 1 - 9 = i - 10 := by omega
      simp [packedIndex, hgate, hinactive, hnotinput, hi, hsub]
    · have hinactive : ¬ (2 ≤ i ∧ i < 9) := by omega
      have hgate : ¬ (10 ≤ i ∧ i < 10 + ts.length) := by omega
      have hoob : ts[i - 10]? = none := List.getElem?_eq_none (by omega)
      simp [packedIndex, hinactive, hgate, hi, List.getD_eq_getElem?_getD, hoob, inputs]

private structure Recipe where
  isOr : Bool
  a : Wire
  b : Wire

private def convert (n : ℕ) (g : Gate) : Recipe :=
  let isOr := match g.op with
    | .or => true
    | _ => false
  let index := fun i => BitVec.ofNat 4 (packedIndex n i)
  match g.inputs with
  | [] => if isOr then ⟨true, 0, 0⟩ else ⟨false, 1, 1⟩
  | [i] => ⟨isOr, index i, index i⟩
  | i :: j :: _ => ⟨isOr, index i, index j⟩

private def convertList (n : ℕ) : List Gate → List Recipe
  | [] => []
  | g :: gs => convert n g :: convertList (n + 1) gs

@[simp] private theorem convertList_length (n : ℕ) (gs : List Gate) :
    (convertList n gs).length = gs.length := by
  induction gs generalizing n with
  | nil => rfl
  | cons g gs ih => simp [convertList, ih]

private def value (ts : List Table) (r : Recipe) : Table :=
  gate (inputs ++ ts) r.isOr r.a r.b

private def run (ts : List Table) (rs : List Recipe) : List Table :=
  rs.foldl (fun w r => w ++ [value w r]) ts

private def boolStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem convert_correct (ts : List Table) (g : Gate) (hn : ts.length ≤ 7)
    (hop : g.op = .and ∨ g.op = .or) (harity : g.inputs.length ≤ 2) (k : Fin 12) :
    (value ts (convert ts.length g)).getLsbD k.val =
      g.op.eval (g.inputs.map fun i =>
        ((originalInputs ++ ts).map (·.getLsbD k.val)).getD i false) := by
  obtain ⟨op, args⟩ := g
  change op = .and ∨ op = .or at hop
  change args.length ≤ 2 at harity
  have hread : ∀ i,
      (read (inputs ++ ts) (BitVec.ofNat 4 (packedIndex ts.length i))).getLsbD k.val =
        ((originalInputs ++ ts).map (·.getLsbD k.val)).getD i false :=
    fun i => by rw [wire_map ts i hn, map_getD_bit]
  have hone : (read (inputs ++ ts) 1).getLsbD k.val = true := by
    change (4095 : Table).getLsbD k.val = true
    exact (by decide +kernel : ∀ j : Fin 12, (4095 : Table).getLsbD j.val = true) k
  have hzero : (read (inputs ++ ts) 0).getLsbD k.val = false := by
    change (0 : Table).getLsbD k.val = false
    exact BitVec.getLsbD_zero
  rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · rcases hop with rfl | rfl
    · change (read (inputs ++ ts) 1 &&& read (inputs ++ ts) 1).getLsbD k.val = true
      rw [BitVec.and_self, hone]
    · change (read (inputs ++ ts) 0 ||| read (inputs ++ ts) 0).getLsbD k.val = false
      rw [BitVec.or_self, hzero]
  · rcases hop with rfl | rfl <;>
      simp only [value, convert, gate, GateOp.eval, Bool.false_eq_true, reduceIte, List.map,
        List.all, List.any, id, BitVec.and_self, BitVec.or_self, hread, Bool.and_true, Bool.or_false]
  · rcases hop with rfl | rfl <;>
      simp only [value, convert, gate, GateOp.eval, Bool.false_eq_true, reduceIte, List.map,
        List.all, List.any, id, BitVec.getLsbD_and, BitVec.getLsbD_or, hread, Bool.and_true, Bool.or_false]
  · simp at harity

private theorem simulate (gs : List Gate) (ts : List Table)
    (hb : ts.length + gs.length ≤ 7)
    (hmono : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (k : Fin 12) :
    (originalInputs ++ run ts (convertList ts.length gs)).map (·.getLsbD k.val) =
      gs.foldl boolStep ((originalInputs ++ ts).map (·.getLsbD k.val)) := by
  induction gs generalizing ts with
  | nil => rfl
  | cons g gs ih =>
    let t := value ts (convert ts.length g)
    have hnew : (ts ++ [t]).length = ts.length + 1 := by simp
    have hbl : (ts ++ [t]).length + gs.length ≤ 7 := by
      simp only [hnew, List.length_cons] at *
      omega
    have hgate := hmono g (by simp)
    have hcorrect := convert_correct ts g (by simp only [List.length_cons] at hb; omega)
      hgate.1 hgate.2 k
    change (originalInputs ++ run (ts ++ [t]) (convertList (ts.length + 1) gs)).map
        (·.getLsbD k.val) =
      gs.foldl boolStep (boolStep ((originalInputs ++ ts).map (·.getLsbD k.val)) g)
    rw [← hnew, ih (ts ++ [t]) hbl (fun g hg => hmono g (by simp [hg]))]
    simp only [boolStep, ← List.append_assoc, List.map_append, List.map_cons, List.map_nil]
    rw [show t.getLsbD k.val = _ from hcorrect]
    rw [List.map_append]

private theorem run_append (ts : List Table) (rs ss : List Recipe) :
    run ts (rs ++ ss) = run (run ts rs) ss := List.foldl_append

private theorem run_length (ts : List Table) (rs : List Recipe) :
    (run ts rs).length = ts.length + rs.length := by
  induction rs generalizing ts with
  | nil => simp [run]
  | cons r rs ih =>
    change (run (ts ++ [value ts r]) rs).length = _
    rw [ih]
    simp
    omega

private theorem run_extends (ts : List Table) (rs : List Recipe) :
    ∃ us, run ts rs = ts ++ us := by
  induction rs generalizing ts with
  | nil => exact ⟨[], by simp [run]⟩
  | cons r rs ih =>
    obtain ⟨us, hu⟩ := ih (ts ++ [value ts r])
    refine ⟨value ts r :: us, ?_⟩
    change run (ts ++ [value ts r]) rs = _
    simpa [List.append_assoc] using hu

private theorem run7 (rs : List Recipe) (h : rs.length = 7) (o : Wire) :
    read (inputs ++ run [] rs) o ≠ 3187 := by
  rcases rs with _ | ⟨r₀, _ | ⟨r₁, _ | ⟨r₂, _ | ⟨r₃, _ | ⟨r₄, _ | ⟨r₅, _ |
    ⟨r₆, _ | ⟨r₇, rest⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals simp only [List.length_nil, List.length_cons] at h
  all_goals try omega
  exact no_packed_witness r₀.a r₀.b r₁.a r₁.b r₂.a r₂.b r₃.a r₃.b r₄.a r₄.b
    r₅.a r₅.b r₆.a r₆.b o r₀.isOr r₁.isOr r₂.isOr r₃.isOr r₄.isOr r₅.isOr r₆.isOr
    _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl

private theorem packed_at_most (rs : List Recipe) (h : rs.length ≤ 7)
    (o : Wire) (ho : o.toNat < (inputs ++ run [] rs).length) :
    read (inputs ++ run [] rs) o ≠ 3187 := by
  let pad := List.replicate (7 - rs.length) (⟨false, 0, 0⟩ : Recipe)
  have hlen : (rs ++ pad).length = 7 := by simp [pad]; omega
  obtain ⟨us, hu⟩ := run_extends (run [] rs) pad
  have hp := run7 (rs ++ pad) hlen o
  rwa [run_append, hu, ← List.append_assoc, read_eq, appendLookup, ite_eq_left ho, ← read_eq] at hp

private theorem project_to_packed (h : RepSizeAtMost target 7) :
    ∃ rs : List Recipe, rs.length ≤ 7 ∧ ∃ o : Wire,
      o.toNat < (inputs ++ run [] rs).length ∧ read (inputs ++ run [] rs) o = 3187 := by
  obtain ⟨C, hmono, hsize, hrep⟩ := h
  have hbudget : C.gates.length ≤ 7 := hsize
  have hgate : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hmono g hg
  let rs := convertList 0 C.gates
  let ts := run [] rs
  have hlen : ts.length = C.gates.length := by simp [ts, rs, run_length]
  let o := BitVec.ofNat 4 (packedIndex ts.length C.output)
  have ho : o.toNat < (inputs ++ ts).length := by
    rw [show o.toNat = packedIndex ts.length C.output by
      exact Nat.mod_eq_of_lt (packedIndex_lt _ _ (by omega))]
    have hi : inputs.length = 9 := rfl
    rw [List.length_append, hi]
    unfold packedIndex
    split
    · omega
    · split <;> omega
  refine ⟨rs, by simpa [rs] using hbudget, o, ho, ?_⟩
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  let k : Fin 12 := ⟨i, hi⟩
  rw [wire_map ts C.output (by omega), map_getD_bit]
  have hsim := simulate C.gates [] (by simpa using hbudget) hgate k
  change (originalInputs ++ ts).map (fun t : Table => t.getLsbD k.val) =
      C.gates.foldl boolStep ((originalInputs ++ []).map (fun t : Table => t.getLsbD k.val)) at hsim
  rw [List.append_nil, initial_bits] at hsim
  change ((originalInputs ++ ts).map (·.getLsbD k.val)).getD C.output false =
    (3187 : Table).getLsbD k.val
  rw [hsim, target_bits]
  exact hrep (row k) (col k)

theorem not_rep_size_at_most_seven : ¬ RepSizeAtMost target 7 := by
  intro h
  obtain ⟨rs, hlen, o, ho, hvalue⟩ := project_to_packed h
  exact packed_at_most rs hlen o ho hvalue

theorem rep_size_at_most_eight : RepSizeAtMost target 8 := by
  refine ⟨⟨[⟨.or, [2, 3]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [10, 11]⟩, ⟨.and, [3, 7]⟩,
    ⟨.or, [7, 8]⟩, ⟨.and, [4, 14]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [16, 15]⟩], 17⟩, ?_⟩
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end ActiveBudget20754
