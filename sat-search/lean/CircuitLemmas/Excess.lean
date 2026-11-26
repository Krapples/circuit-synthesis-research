/-
Restriction excess (2026-11-26).

`excess_restriction`: in the free-NOT binary AIG model of `GateElim`, if every input in `F` is essential
for `f` and `f` with the inputs of `F` fixed is still nonconstant, then
`C(f restricted) ≤ C(f) - |F|`, i.e. `C(f) ≥ C(f|ρ) + |dom ρ|`. With `F` the inputs fixed by a block
restriction of a fully supported `f`, this is the excess inequality `B ≥ n - m + C(f|ρ)` used by the
SAT gate-elimination bounds (claim 6 of NOTES_SAT_ENCODING_BOUNDS.md), where the paper proof uses the cycle
rank of the circuit graph.

Proof (a direct counting argument in place of graph minors). Take a circuit of minimum size. Under the
restriction call a wire *constant* if its value does not depend on the free inputs.
* Every input of `F` is read by a gate (it is essential, and the output reading it directly would make the
  restriction constant), and every constant gate is read by a later gate (a minimum circuit has no dead
  gate, and a constant output would make the restriction constant). So at least `|F| + #constant gates`
  distinct constant wires are read.
* A constant gate has at most two operand slots that read constant wires; a nonconstant gate has at most
  one (two would make it constant). So at most `2 #constant gates + #other gates with a constant operand`
  constant wires are read.
* Hence `|F| ≤ #gates with a constant operand or constant value`, and every such gate is degenerate in
  the restricted circuit, so `bypass_many` deletes them all.
-/
import CircuitLemmas.GateElim

namespace CircuitLemmas.GateElim

/-! ## Fixing a set of inputs -/

/-- `x` with every input in `F` set to its value in `b`. -/
def fixS (F : Finset ℕ) (b : ℕ → Bool) (x : ℕ → Bool) : ℕ → Bool :=
  fun w => if w ∈ F then b w else x w

def Ref.restrictS (n : ℕ) (F : Finset ℕ) (b : ℕ → Bool) : Ref → Ref
  | .const c => .const c
  | .wire w neg => if w < n ∧ w ∈ F then .const (Bool.xor (b w) neg) else .wire w neg

def Gate.restrictS (n : ℕ) (F : Finset ℕ) (b : ℕ → Bool) (g : Gate) : Gate :=
  ⟨g.a.restrictS n F b, g.b.restrictS n F b⟩

section restrictS

variable (n : ℕ) (F : Finset ℕ) (b : ℕ → Bool)

theorem restrictS_ref (x : ℕ → Bool) (rgs : List Gate)
    (h : ∀ w, ¬ (w < n ∧ w ∈ F) →
      val n x (rgs.map (Gate.restrictS n F b)) w = val n (fixS F b x) rgs w) (r : Ref) :
    (r.restrictS n F b).eval (val n x (rgs.map (Gate.restrictS n F b))) =
      r.eval (val n (fixS F b x) rgs) := by
  cases r with
  | const c => rfl
  | wire w neg =>
      by_cases hw : w < n ∧ w ∈ F
      · simp only [Ref.restrictS]
        rw [if_pos hw]
        simp only [Ref.eval]
        rw [val_input n _ rgs w hw.1]
        simp [fixS, hw.2]
      · simp only [Ref.restrictS]
        rw [if_neg hw]
        simp only [Ref.eval]
        rw [h w hw]

theorem restrictS_val (x : ℕ → Bool) :
    ∀ (rgs : List Gate) (w : ℕ), ¬ (w < n ∧ w ∈ F) →
      val n x (rgs.map (Gate.restrictS n F b)) w = val n (fixS F b x) rgs w
  | [], w, hw => by
      simp only [List.map_nil, val]
      by_cases h : w < n
      · rw [if_pos h, if_pos h]
        have : w ∉ F := fun hF => hw ⟨h, hF⟩
        simp [fixS, this]
      · rw [if_neg h, if_neg h]
  | g :: rgs, w, hw => by
      have ih := restrictS_val x rgs
      simp only [List.map_cons, val, List.length_map]
      by_cases htop : w = n + rgs.length
      · rw [if_pos htop, if_pos htop]
        simp only [Gate.eval, Gate.restrictS]
        rw [restrictS_ref n F b x rgs ih g.a, restrictS_ref n F b x rgs ih g.b]
      · rw [if_neg htop, if_neg htop]
        exact ih w hw

/-! ## Constant wires under the restriction -/

/-- Wire `w` (as seen after the gates `rgs`) is constant once the inputs of `F` are fixed. -/
def CW (rgs : List Gate) (w : ℕ) : Prop := ∃ c, ∀ x, val n (fixS F b x) rgs w = c

/-- The operand is a constant or reads a constant wire. -/
def RC (rgs : List Gate) : Ref → Prop
  | .const _ => True
  | .wire w _ => CW n F b rgs w

/-- The gate, placed after `rgs`, is constant once the inputs of `F` are fixed. -/
def GC (rgs : List Gate) (g : Gate) : Prop := ∃ c, ∀ x, g.eval (val n (fixS F b x) rgs) = c

theorem RC_eval (rgs : List Gate) (r : Ref) (h : RC n F b rgs r) :
    ∃ c, ∀ x, r.eval (val n (fixS F b x) rgs) = c := by
  cases r with
  | const c => exact ⟨c, fun _ => rfl⟩
  | wire w neg =>
      obtain ⟨c, hc⟩ := h
      exact ⟨Bool.xor c neg, fun x => by simp [Ref.eval, hc x]⟩

theorem GC_of_RC (rgs : List Gate) (g : Gate) (ha : RC n F b rgs g.a) (hb : RC n F b rgs g.b) :
    GC n F b rgs g := by
  obtain ⟨ca, hca⟩ := RC_eval n F b rgs g.a ha
  obtain ⟨cb, hcb⟩ := RC_eval n F b rgs g.b hb
  exact ⟨ca && cb, fun x => by simp [Gate.eval, hca x, hcb x]⟩

/-- A gate with a constant operand or a constant value is degenerate in the restricted circuit. -/
theorem degenerate_restrictS (rgs : List Gate) (g : Gate)
    (h : GC n F b rgs g ∨ RC n F b rgs g.a ∨ RC n F b rgs g.b) :
    Degenerate n (g.restrictS n F b) (rgs.map (Gate.restrictS n F b)) := by
  have hr : ∀ x (r : Ref), (r.restrictS n F b).eval (val n x (rgs.map (Gate.restrictS n F b))) =
      r.eval (val n (fixS F b x) rgs) := fun x => restrictS_ref n F b x rgs (restrictS_val n F b x rgs)
  rcases h with hg | ha | hb
  · obtain ⟨c, hc⟩ := hg
    refine ⟨.const c, fun x => ?_⟩
    simp only [Gate.eval, Gate.restrictS]
    rw [hr x g.a, hr x g.b]
    exact hc x
  · obtain ⟨c, hc⟩ := RC_eval n F b rgs g.a ha
    refine ⟨if c then g.b.restrictS n F b else .const false, fun x => ?_⟩
    simp only [Gate.eval, Gate.restrictS]
    rw [hr x g.a, hc x]
    cases c <;> simp [Ref.eval]
  · obtain ⟨c, hc⟩ := RC_eval n F b rgs g.b hb
    refine ⟨if c then g.a.restrictS n F b else .const false, fun x => ?_⟩
    simp only [Gate.eval, Gate.restrictS]
    rw [hr x g.b, hc x]
    cases c <;> simp [Ref.eval]

/-! ## Counting -/

open Classical in
/-- Weight 2 for a constant gate, 1 for another gate with a constant operand, else 0. -/
noncomputable def wt : List Gate → ℕ
  | [] => 0
  | g :: rgs => (if GC n F b rgs g then 2 else if RC n F b rgs g.a ∨ RC n F b rgs g.b then 1 else 0) +
      wt rgs

open Classical in
/-- The wires of the constant gates. -/
noncomputable def kw : List Gate → Finset ℕ
  | [] => ∅
  | g :: rgs => (if GC n F b rgs g then {n + rgs.length} else ∅) ∪ kw rgs

open Classical in
/-- The constant wires that an operand reads. -/
noncomputable def cref (rgs : List Gate) : Ref → Finset ℕ
  | .const _ => ∅
  | .wire w _ => if CW n F b rgs w then {w} else ∅

/-- The constant wires read by some gate. -/
noncomputable def rdS : List Gate → Finset ℕ
  | [] => ∅
  | g :: rgs => rdS rgs ∪ (cref n F b rgs g.a ∪ cref n F b rgs g.b)

theorem kw_bound : ∀ (rgs : List Gate), ∀ w ∈ kw n F b rgs, n ≤ w ∧ w < n + rgs.length
  | [], w, hw => by simp [kw] at hw
  | g :: rgs, w, hw => by
      simp only [kw, Finset.mem_union] at hw
      rcases hw with hw | hw
      · split_ifs at hw with h
        · simp only [Finset.mem_singleton] at hw; simp [hw]
        · simp at hw
      · have := kw_bound rgs w hw; simp only [List.length_cons]; omega

theorem wt_le : ∀ (rgs : List Gate),
    wt n F b rgs ≤ degCount n (rgs.map (Gate.restrictS n F b)) + (kw n F b rgs).card
  | [] => by simp [wt]
  | g :: rgs => by
      have ih := wt_le rgs
      have hnot : n + rgs.length ∉ kw n F b rgs := fun h => by
        have := kw_bound n F b rgs _ h; omega
      simp only [wt, List.map_cons, degCount, kw]
      by_cases hg : GC n F b rgs g
      · have hd := degenerate_restrictS n F b rgs g (Or.inl hg)
        rw [if_pos hg, if_pos hd, if_pos hg, Finset.card_union_of_disjoint
          (Finset.disjoint_singleton_left.mpr hnot), Finset.card_singleton]
        omega
      · rw [if_neg hg, if_neg hg, Finset.empty_union]
        by_cases hr : RC n F b rgs g.a ∨ RC n F b rgs g.b
        · have hd := degenerate_restrictS n F b rgs g (Or.inr hr)
          rw [if_pos hr, if_pos hd]
          omega
        · rw [if_neg hr]
          split_ifs <;> omega

open Classical in
theorem card_cref_le (rgs : List Gate) (r : Ref) :
    (cref n F b rgs r).card ≤ if RC n F b rgs r then 1 else 0 := by
  cases r with
  | const c => simp [cref]
  | wire w neg =>
      simp only [cref, RC]
      by_cases h : CW n F b rgs w <;> simp [h]

open Classical in
theorem card_rdS_le : ∀ (rgs : List Gate), (rdS n F b rgs).card ≤ wt n F b rgs
  | [] => by simp [rdS]
  | g :: rgs => by
      have ih := card_rdS_le rgs
      have h1 := Finset.card_union_le (rdS n F b rgs) (cref n F b rgs g.a ∪ cref n F b rgs g.b)
      have h2 := Finset.card_union_le (cref n F b rgs g.a) (cref n F b rgs g.b)
      have ha := card_cref_le n F b rgs g.a
      have hb := card_cref_le n F b rgs g.b
      simp only [rdS, wt]
      by_cases hg : GC n F b rgs g
      · rw [if_pos hg]
        split_ifs at ha hb <;> omega
      · rw [if_neg hg]
        by_cases hra : RC n F b rgs g.a
        · have hrb : ¬ RC n F b rgs g.b := fun hrb => hg (GC_of_RC n F b rgs g hra hrb)
          rw [if_pos (Or.inl hra)]
          rw [if_pos hra] at ha; rw [if_neg hrb] at hb
          omega
        · rw [if_neg hra] at ha
          by_cases hrb : RC n F b rgs g.b
          · rw [if_pos (Or.inr hrb)]; rw [if_pos hrb] at hb; omega
          · rw [if_neg (by tauto)]; rw [if_neg hrb] at hb; omega

theorem rdS_append : ∀ (later earlier : List Gate), rdS n F b earlier ⊆ rdS n F b (later ++ earlier)
  | [], _ => by simp
  | g :: later, earlier => by
      simp only [List.cons_append, rdS]
      exact (rdS_append later earlier).trans Finset.subset_union_left

/-- A gate reading a constant wire puts it in `rdS`. -/
theorem mem_rdS (later earlier : List Gate) (g : Gate) (w : ℕ) (hw : CW n F b earlier w)
    (hr : g.a.Reads w ∨ g.b.Reads w) : w ∈ rdS n F b (later ++ g :: earlier) := by
  apply rdS_append n F b later
  simp only [rdS, Finset.mem_union]
  right
  rcases hr with hr | hr
  · left
    cases h : g.a with
    | const c => rw [h] at hr; simp [Ref.Reads] at hr
    | wire w' neg =>
        rw [h] at hr; simp only [Ref.Reads] at hr; subst hr
        simp [cref, hw]
  · right
    cases h : g.b with
    | const c => rw [h] at hr; simp [Ref.Reads] at hr
    | wire w' neg =>
        rw [h] at hr; simp only [Ref.Reads] at hr; subst hr
        simp [cref, hw]

theorem mem_kw : ∀ (rgs : List Gate) (w : ℕ), w ∈ kw n F b rgs →
    ∃ later g earlier, rgs = later ++ g :: earlier ∧ GC n F b earlier g ∧ w = n + earlier.length
  | [], w, hw => by simp [kw] at hw
  | g :: rgs, w, hw => by
      simp only [kw, Finset.mem_union] at hw
      rcases hw with hw | hw
      · split_ifs at hw with h
        · simp only [Finset.mem_singleton] at hw
          exact ⟨[], g, rgs, rfl, h, hw⟩
        · simp at hw
      · obtain ⟨l, g', e, he, hg, hw⟩ := mem_kw rgs w hw
        exact ⟨g :: l, g', e, by simp [he], hg, hw⟩

/-- **Counting core.** If every input of `F` is read by some gate and every constant gate has a later
reader, then at least `|F|` gates are degenerate in the restricted circuit. -/
theorem card_le_degCount (rgs : List Gate) (hFn : ∀ z ∈ F, z < n)
    (hF : ∀ z ∈ F, ∃ g ∈ rgs, g.a.Reads z ∨ g.b.Reads z)
    (hlive : ∀ later g earlier, rgs = later ++ g :: earlier → GC n F b earlier g →
      ∃ g' ∈ later, g'.a.Reads (n + earlier.length) ∨ g'.b.Reads (n + earlier.length)) :
    F.card ≤ degCount n (rgs.map (Gate.restrictS n F b)) := by
  have hsub : F ∪ kw n F b rgs ⊆ rdS n F b rgs := by
    intro w hw
    rcases Finset.mem_union.mp hw with hwF | hwK
    · obtain ⟨g, hg, hr⟩ := hF w hwF
      obtain ⟨s, t, rfl⟩ := List.append_of_mem hg
      refine mem_rdS n F b s t g w ⟨b w, fun x => ?_⟩ hr
      rw [val_input n _ t w (hFn w hwF)]
      simp [fixS, hwF]
    · obtain ⟨later, g, earlier, he, hg, rfl⟩ := mem_kw n F b rgs w hwK
      obtain ⟨g', hg', hr⟩ := hlive later g earlier he hg
      obtain ⟨s, t, rfl⟩ := List.append_of_mem hg'
      obtain ⟨c, hc⟩ := hg
      have he' : rgs = s ++ g' :: (t ++ g :: earlier) := by simp [he]
      rw [he']
      refine mem_rdS n F b s (t ++ g :: earlier) g' _ ⟨c, fun x => ?_⟩ hr
      rw [val_append_lt n _ (g :: earlier) t _ (by simp)]
      simpa [val] using hc x
  have hdisj : Disjoint F (kw n F b rgs) := by
    rw [Finset.disjoint_left]
    intro w hw hk
    have := kw_bound n F b rgs w hk
    have := hFn w hw
    omega
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj] at h1
  have h2 := card_rdS_le n F b rgs
  have h3 := wt_le n F b rgs
  omega

end restrictS

/-! ## The excess inequality -/

theorem eval_fixS_const_of_out {C : Circuit} {F : Finset ℕ} {b : ℕ → Bool} {z : ℕ} {neg : Bool}
    (hz : z < C.n) (hzF : z ∈ F) (ho : C.out = .wire z neg) (x : ℕ → Bool) :
    C.eval (fixS F b x) = Bool.xor (b z) neg := by
  simp only [Circuit.eval, ho, Ref.eval]
  rw [val_input C.n _ C.rgates z hz]
  simp [fixS, hzF]

/-- **Restriction excess.** If every input of `F` is essential for `f` and `f` with the inputs of `F`
fixed to `b` is nonconstant, then fixing them saves at least `|F|` gates: `C(f|ρ) ≤ C(f) - |F|`. -/
theorem excess_restriction {n s : ℕ} {f : (ℕ → Bool) → Bool} (F : Finset ℕ) (b : ℕ → Bool)
    (hFn : ∀ z ∈ F, z < n) (hess : ∀ z ∈ F, ∃ x, f (upd x z true) ≠ f (upd x z false))
    (hnc : ∃ x y, f (fixS F b x) ≠ f (fixS F b y)) (h : Realizes n f s) :
    Realizes n (fun x => f (fixS F b x)) (s - F.card) := by
  classical
  have hex : ∃ s, Realizes n f s := ⟨s, h⟩
  obtain ⟨C, hn, hs, hf⟩ := Nat.find_spec hex
  have hle : Nat.find hex ≤ s := Nat.find_min' hex h
  -- minimality: no circuit for `f` is smaller than `C`
  have hmin : ∀ C' : Circuit, C'.n = n → (∀ x, C'.eval x = f x) → C.size ≤ C'.size := fun C' hn' hf' =>
    hs.trans (Nat.find_min' hex ⟨C', hn', le_rfl, hf'⟩)
  obtain ⟨x0, y0, hxy⟩ := hnc
  -- a constant restricted output is impossible
  have hconst : ∀ c, ¬ ∀ x, C.eval (fixS F b x) = c := fun c hc => hxy (by rw [← hf, ← hf, hc, hc])
  have hF : ∀ z ∈ F, ∃ g ∈ C.rgates, g.a.Reads z ∨ g.b.Reads z := by
    intro z hz
    by_contra hno
    simp only [not_exists, not_and, not_or] at hno
    have hzn : z < C.n := hn ▸ hFn z hz
    by_cases ho : C.out.Reads z
    · cases hout : C.out with
      | const c => rw [hout] at ho; simp [Ref.Reads] at ho
      | wire w neg =>
          rw [hout] at ho; simp only [Ref.Reads] at ho; subst ho
          exact hconst _ (eval_fixS_const_of_out hzn hz hout)
    · obtain ⟨x, hx⟩ := hess z hz
      apply hx
      rw [← hf, ← hf, C.eval_upd_of_not_reads z true hzn (fun g hg => by
          have := hno g hg; tauto) ho,
        C.eval_upd_of_not_reads z false hzn (fun g hg => by have := hno g hg; tauto) ho]
  have hlive : ∀ later g earlier, C.rgates = later ++ g :: earlier → GC C.n F b earlier g →
      ∃ g' ∈ later, g'.a.Reads (C.n + earlier.length) ∨ g'.b.Reads (C.n + earlier.length) := by
    intro later g earlier he hg
    by_contra hno
    simp only [not_exists, not_and, not_or] at hno
    by_cases ho : C.out.Reads (C.n + earlier.length)
    · obtain ⟨c, hc⟩ := hg
      cases hout : C.out with
      | const c' => rw [hout] at ho; simp [Ref.Reads] at ho
      | wire w neg =>
          rw [hout] at ho; simp only [Ref.Reads] at ho; subst ho
          refine hconst (Bool.xor c neg) fun x => ?_
          simp only [Circuit.eval, hout, Ref.eval, he]
          rw [val_append_lt C.n _ (g :: earlier) later _ (by simp)]
          simp [val, hc x]
    · obtain ⟨C', hn', hs', he'⟩ := delete_dead C later earlier g he
        (fun g' hg' => by have := hno g' hg'; tauto) ho
      have := hmin C' (hn'.trans hn) (fun x => by rw [he', hf])
      omega
  have hcount := card_le_degCount C.n F b C.rgates (fun z hz => hn ▸ hFn z hz) hF hlive
  obtain ⟨C', hn', hs', he', -⟩ := bypass_many C.n (C.rgates.map (Gate.restrictS C.n F b)) []
    (C.out.restrictS C.n F b)
  refine ⟨C', hn'.trans hn, ?_, fun x => ?_⟩
  · simp only [List.nil_append, List.length_map] at hs'
    simp only [Circuit.size] at hs
    omega
  · rw [he' x]
    show _ = f (fixS F b x)
    rw [← hf]
    exact restrictS_ref C.n F b x C.rgates (restrictS_val C.n F b x C.rgates) C.out

end CircuitLemmas.GateElim
