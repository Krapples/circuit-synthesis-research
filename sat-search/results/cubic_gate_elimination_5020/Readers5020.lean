import PEqualNP.MetaComplexity.Helpers.ReadersPat

namespace Readers5020

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers

variable {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}

private theorem false_status (L : Least (n + 1) f gs o)
    (v : Fin (n + 1)) {p : ℕ} {g : Gate}
    (hg : gs[p]? = some g) (hv : v.val ∈ g.inputs)
    (hnon : g.op ≠ .or) :
    (g.op = .and ∧ stF n gs v false (n + 1 + p) = Stat.const false) ∨
    (g.op = .not ∧ stF n gs v false (n + 1 + p) = Stat.const true) := by
  obtain ⟨t, ht⟩ := st_gate n gs L.hcl v false p g hg
  rcases L.hcl p g hg with ⟨hop, j, _, hin⟩ | ⟨hop, j, k, _, _, hin⟩
  · have hj : v.val = j := by simpa [hin] using hv
    refine Or.inr ⟨hop, ?_⟩
    simp [ht, hop, hin, ← hj, stF_self, simplify, simpNot]
  · have ho : g.op = .and := hop.resolve_right hnon
    have hmem : v.val = j ∨ v.val = k := by simpa [hin] using hv
    refine Or.inl ⟨ho, ?_⟩
    rcases hmem with hj | hk
    · rw [ht, ho, hin, ← hj]
      simp only [List.map_cons, List.map_nil, stF_self, simplify]
      cases stF n gs v false k <;> rfl
    · rw [ht, ho, hin, ← hk]
      simp only [List.map_cons, List.map_nil, stF_self, simplify]
      cases stF n gs v false j with
      | const c => cases c <;> rfl
      | wire j => rfl

/-- If two effective readers survive the input syntax and at least one is not
an OR, either false restriction saves four gates or the non-OR reader has a
single later consumer whose operation is transparent to its restricted value. -/
theorem four_or_transparent (L : Least (n + 1) f gs o) (v : Fin (n + 1))
    (hNC : ∃ x y, f (Function.update x v false) ≠ f (Function.update y v false))
    {p q : ℕ} {gp gq : Gate} (hpq : p ≠ q)
    (hgp : gs[p]? = some gp) (hgq : gs[q]? = some gq)
    (hip : v.val ∈ gp.inputs) (hiq : v.val ∈ gq.inputs)
    (hnon : gp.op ≠ .or) :
    Drop f v false 4 gs.length ∨
      gq.op = .or ∧ ∃ r g, r ≠ p ∧ r ≠ q ∧ gs[r]? = some g ∧
        n + 1 + p ∈ g.inputs ∧
        (∀ s, Reads gs s (n + 1 + p) → s = r) ∧
        ((gp.op = .and ∧ g.op = .or) ∨ (gp.op = .not ∧ g.op = .and)) := by
  classical
  have hp : Reads gs p v := ⟨gp, hgp, hip⟩
  have hq : Reads gs q v := ⟨gq, hgq, hiq⟩
  have hfnc : ∃ x y, f x ≠ f y := by
    obtain ⟨x, y, h⟩ := hNC
    exact ⟨_, _, h⟩
  have hps := false_status L v hgp hip hnon
  have hpc : IsC n gs v false (n + 1 + p) := by
    rcases hps with ⟨_, h⟩ | ⟨_, h⟩
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩
  by_cases hor : gq.op = .or
  · obtain ⟨r, hrp, hr, hrc⟩ := L.next v false hNC p (reads_len hp) hpc
    have hrq : r ≠ q := fun e => L.no_tri hfnc p q v hp hq (e ▸ hr)
    by_cases hd : Drop f v false 4 gs.length
    · exact Or.inl hd
    · right
      have only : ∀ s, Reads gs s (n + 1 + p) → s = r := by
        intro s hs
        by_contra hsr
        have hsp := reads_lt L.hcl hs
        have hsq : s ≠ q := fun e => L.no_tri hfnc p q v hp hq (e ▸ hs)
        exact hd (L.save4 v false hNC p q r s hpq (by omega) (by omega)
          hrq.symm hsq.symm (Ne.symm hsr) (rc_input false hp) (rc_input false hq) hrc
          (rc_of_reads hs hpc))
      obtain ⟨gr, hgr, hKin⟩ := hr
      have hnotc : ¬ IsC n gs v false (n + 1 + r) := by
        intro hc
        obtain ⟨s, hsr, hs, hsc⟩ := L.next v false hNC r
          (reads_len ⟨gr, hgr, hKin⟩) hc
        have hsq : s ≠ q := by
          intro e
          subst s
          obtain ⟨gq', hq', hqread⟩ := hs
          have eq : gq' = gq := Option.some.inj (hq'.symm.trans hgq)
          subst gq'
          have bad : IsC n gs v false (n + 1 + q) :=
            st_allconst n gs L.hcl v false q gq hgq (fun w hw => by
              rcases two_inputs (L.hcl q gq hgq) v.val (n + 1 + r) w hiq hqread
                (by have := v.isLt; omega) hw with he | he
              · exact ⟨false, he ▸ stF_self n gs v false⟩
              · exact he ▸ hc)
          exact hd (L.fourth v false hNC p q hpq hp hq hpc bad)
        exact hd (L.save4 v false hNC p q r s hpq (by omega) (by omega)
          hrq.symm hsq.symm (by omega) (rc_input false hp) (rc_input false hq) hrc hsc)
      refine ⟨hor, r, gr, by omega, hrq, hgr, hKin, only, ?_⟩
      rcases hps with ⟨hpa, hstat⟩ | ⟨hpn, hstat⟩
      · have ⟨hops, hbit, _⟩ := st_shape n gs L.hcl v false r gr hgr _
          hKin false hstat (fun c he => hnotc ⟨c, he⟩)
        exact Or.inl ⟨hpa, hops.resolve_left (fun ha => hbit (by simp [fixBit, ha]))⟩
      · have ⟨hops, hbit, _⟩ := st_shape n gs L.hcl v false r gr hgr _
          hKin true hstat (fun c he => hnotc ⟨c, he⟩)
        exact Or.inr ⟨hpn, hops.resolve_right (fun ho => hbit (by simp [fixBit, ho]))⟩
  · left
    apply L.fourth v false hNC p q hpq hp hq hpc
    rcases false_status L v hgq hiq hor with ⟨_, h⟩ | ⟨_, h⟩
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩

private theorem emitted_clean (acc : List Stat × List Gate) (N : ℕ) (g : Gate)
    (hok : NOk g)
    (emitted : (elimStep N acc g).2.length ≠ acc.2.length) :
    CleanGate acc.1.length g := by
  have hwire : ∀ j ∈ g.inputs, j < acc.1.length := by
    intro j hmem
    by_contra! hj
    have hconst := List.getD_eq_default acc.1 (Stat.const false) hj
    exact emitted (elimStep_none N acc g hok j hmem false hconst)
  obtain ⟨op, ins⟩ := g
  rcases hok.1.1 with hop | hop | hop
  · change op = .and at hop
    subst op
    right
    refine ⟨Or.inl rfl, ?_⟩
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨i, t⟩⟩⟩
    · exact (emitted (by simp [elimStep, simplify, simpAnd])).elim
    · exfalso
      apply emitted
      change (acc.2 ++ (simpAnd (N + acc.2.length) [acc.1.getD a (.const false)]).1.toList).length = _
      cases acc.1.getD a (Stat.const false) <;> simp [simpAnd]
    · exact ⟨a, b, hwire _ (by simp), hwire _ (by simp), rfl⟩
    · have hlen := hok.1.2
      simp at hlen
  · change op = .or at hop
    subst op
    right
    refine ⟨Or.inr rfl, ?_⟩
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨i, t⟩⟩⟩
    · exact (emitted (by simp [elimStep, simplify, simpOr])).elim
    · exfalso
      apply emitted
      change (acc.2 ++ (simpOr (N + acc.2.length) [acc.1.getD a (.const false)]).1.toList).length = _
      cases acc.1.getD a (Stat.const false) <;> simp [simpOr]
    · exact ⟨a, b, hwire _ (by simp), hwire _ (by simp), rfl⟩
    · have hlen := hok.1.2
      simp at hlen
  · have ho : op = .not := hop
    subst op
    left
    refine ⟨rfl, ?_⟩
    rcases ins with _ | ⟨a, _ | ⟨b, bs⟩⟩
    · exact (emitted (by simp [elimStep, simplify, simpNot])).elim
    · exact ⟨a, hwire _ (by simp), rfl⟩
    · have hlen := hok.2 rfl
      simp at hlen

/-- Trimming ignored NOT operands is enough to make every gate in a minimum
circuit clean, because any other failure to be clean costs an emission. -/
theorem normalized_least {N : ℕ} {F : (Fin N → Bool) → Bool} {C : Circuit}
    (hFan : FanInTwo C) (hFun : circuitFun N C = F)
    (hMin : ∀ s, HasCircuitSize N F s → C.size ≤ s)
    (hNC : ∃ x y, F x ≠ F y) :
    Least N F (C.gates.map normGate) C.output := by
  let G := C.gates.map normGate
  let init : List Stat × List Gate := (idStats N, [])
  have hEval (x : Fin N → Bool) : vl G x C.output = F x := by
    change (wiresFrom (C.gates.map normGate) (List.ofFn x)).getD C.output false = F x
    rw [wiresFrom_norm]
    exact congrFun hFun x
  have hNOk : ∀ g ∈ G, NOk g := by
    intro g hg
    obtain ⟨pre, hpre, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok pre (hFan pre hpre)
  have hOk : ∀ g ∈ G, Ok g := fun g hg => (hNOk g hg).1
  have hminEmit : G.length ≤ (elim N G init).2.length := by
    let done := elim N G init
    have inv (x : Fin N → Bool) :
        Inv N (List.ofFn x) (wiresFrom G (List.ofFn x)) done :=
      inv_elim N _ (by simp) G _ _ hOk (inv_id N x)
    have final (x : Fin N → Bool) :
        (done.1.getD C.output (Stat.const false)).val
          (wiresFrom done.2 (List.ofFn x)) = F x :=
      ((inv x).2 C.output).2.trans (hEval x)
    cases hOut : done.1.getD C.output (Stat.const false) with
    | const b =>
      obtain ⟨x, y, hxy⟩ := hNC
      have hx := final x
      have hy := final y
      rw [hOut] at hx hy
      exact (hxy (hx.symm.trans hy)).elim
    | wire j =>
      have fan : FanInTwo (⟨done.2, j⟩ : Circuit) :=
        elim_ok N G init (by simp [init])
      have hsize : HasCircuitSize N F done.2.length :=
        ⟨⟨done.2, j⟩, fan, le_rfl, fun x => by
          have hx := final x
          rw [hOut] at hx
          exact hx⟩
      simpa [G, Circuit.size] using hMin _ hsize
  refine ⟨?_, hEval, ?_⟩
  · intro p g hg
    obtain ⟨pre, post, hsplit, hlen⟩ := split_at G p g hg
    let acc := elim N pre init
    have hAcc : acc.1.length = N + p := by simp [acc, elim_fst_len, init, idStats, hlen]
    have hp := elim_len N pre init
    have ht := elim_len N post (elimStep N acc g)
    have hmin : pre.length + 1 + post.length ≤ (elim N post (elimStep N acc g)).2.length := by
      rw [hsplit, elim_append, elim_cons] at hminEmit
      simpa [acc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hminEmit
    rw [← hAcc]
    exact emitted_clean acc N g (hNOk g (List.mem_of_getElem? hg)) (fun he => by
      rw [he] at ht
      have : acc.2.length ≤ pre.length := by simpa [acc, init] using hp
      omega)
  · intro G' o' hClean he
    have h := has_of_clean N G' o' hClean
    have hs : HasCircuitSize N F G'.length := by
      simpa [show (fun x => vl G' x o') = F from funext he] using h
    simpa [G, Circuit.size] using hMin _ hs

theorem norm_effective (g : Gate) (hok : Ok g) :
    (normGate g).op = g.op ∧
      (normGate g).inputs = g.inputs.take (bif g.op.eval [false] then 1 else 2) := by
  obtain ⟨op, ins⟩ := g
  have hlen : ins.length ≤ 2 := hok.2
  have hop : op = .and ∨ op = .or ∨ op = .not := hok.1
  rcases hop with rfl | rfl | rfl <;>
    simp [normGate, GateOp.eval, List.take_of_length_le hlen]

private theorem two_positions (gates : List Gate) (reads : Gate → Bool)
    (hTwo : (gates.filter reads).length = 2)
    (hNon : ∃ g ∈ gates.filter reads, g.op ≠ .or) :
    ∃ (p q : ℕ) (gp gq : Gate), p ≠ q ∧ gates[p]? = some gp ∧ gates[q]? = some gq ∧
      reads gp = true ∧ reads gq = true ∧ gp.op ≠ .or := by
  classical
  induction gates with
  | nil => simp at hTwo
  | cons a tl ih =>
    cases hRead : reads a
    · have hTwo' : (tl.filter reads).length = 2 := by simpa [hRead] using hTwo
      have hNon' : ∃ g ∈ tl.filter reads, g.op ≠ .or := by simpa [hRead] using hNon
      obtain ⟨p, q, gp, gq, hpq, hp, hq, hrp, hrq, hn⟩ := ih hTwo' hNon'
      exact ⟨p+1, q+1, gp, gq, by omega, by simpa using hp, by simpa using hq, hrp, hrq, hn⟩
    · have hOne : (tl.filter reads).length = 1 := by simpa [hRead] using hTwo
      by_cases hOp : a.op = .or
      · obtain ⟨g, hmem, hne⟩ := hNon
        have hmem' : g ∈ tl.filter reads := by
          rcases (show g = a ∨ g ∈ tl.filter reads from by simpa [hRead] using hmem) with he | hm
          · exact (hne (he.symm ▸ hOp)).elim
          · exact hm
        obtain ⟨htl, hr⟩ := List.mem_filter.1 hmem'
        obtain ⟨j, hj⟩ := List.getElem?_of_mem htl
        exact ⟨j+1, 0, g, a, by omega, by simpa using hj, rfl, hr, hRead, hne⟩
      · have hne : tl.filter reads ≠ [] := by
          intro he
          simp [he] at hOne
        obtain ⟨g, hmem⟩ := List.exists_mem_of_ne_nil _ hne
        obtain ⟨htl, hr⟩ := List.mem_filter.1 hmem
        obtain ⟨j, hj⟩ := List.getElem?_of_mem htl
        exact ⟨0, j+1, a, g, by omega, rfl, by simpa using hj, hRead, hr, hOp⟩

theorem original_reader_cases (v : Fin (n + 1)) {C : Circuit}
    (hFan : FanInTwo C) (hFun : circuitFun (n + 1) C = f)
    (hMin : ∀ s, HasCircuitSize (n + 1) f s → C.size ≤ s)
    (hNC : ∃ x y, f (Function.update x v false) ≠ f (Function.update y v false))
    (hTwo : (C.gates.filter fun g =>
      (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val).length = 2)
    (hNon : ∃ g ∈ C.gates.filter (fun g =>
      (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val), g.op ≠ .or) :
    Drop f v false 4 C.size ∨
      ∃ p q r gp gq gr, p ≠ q ∧ r ≠ p ∧ r ≠ q ∧
        C.gates[p]? = some gp ∧ C.gates[q]? = some gq ∧ C.gates[r]? = some gr ∧
        v.val ∈ (normGate gp).inputs ∧ v.val ∈ (normGate gq).inputs ∧
        n + 1 + p ∈ (normGate gr).inputs ∧
        (∀ s, Reads (C.gates.map normGate) s (n + 1 + p) → s = r) ∧
        gq.op = .or ∧
        ((gp.op = .and ∧ gr.op = .or) ∨ (gp.op = .not ∧ gr.op = .and)) := by
  classical
  obtain ⟨p, q, gp, gq, hpq, hgp, hgq, hp, hq, hpn⟩ := two_positions C.gates _ hTwo hNon
  have np := norm_effective gp (hFan gp (List.mem_of_getElem? hgp))
  have nq := norm_effective gq (hFan gq (List.mem_of_getElem? hgq))
  have hFn : ∃ x y, f x ≠ f y := by
    obtain ⟨x, y, h⟩ := hNC
    exact ⟨_, _, h⟩
  have L := normalized_least hFan hFun hMin hFn
  have hp' : v.val ∈ (normGate gp).inputs := by simpa [np.2] using hp
  have hq' : v.val ∈ (normGate gq).inputs := by simpa [nq.2] using hq
  have hgp' : (C.gates.map normGate)[p]? = some (normGate gp) := by simp [hgp]
  have hgq' : (C.gates.map normGate)[q]? = some (normGate gq) := by simp [hgq]
  rcases four_or_transparent L v hNC hpq hgp' hgq' hp' hq' (by simpa [np.1]) with h | h
  · exact Or.inl (by simpa [Circuit.size] using h)
  · obtain ⟨hqo, r, gr, hrp, hrq, hgr, hv, hu, hshape⟩ := h
    have hx : (C.gates[r]?).map normGate = some gr := by simpa only [List.getElem?_map] using hgr
    cases hrr : C.gates[r]? with
    | none => simp [hrr] at hx
    | some rr =>
      have he : normGate rr = gr := by simpa [hrr] using hx
      subst gr
      have nr := norm_effective rr (hFan rr (List.mem_of_getElem? hrr))
      exact Or.inr ⟨p, q, r, gp, gq, rr, hpq, hrp, hrq, hgp, hgq, hrr, hp', hq', hv, hu,
        by simpa [nq.1] using hqo, by simpa [np.1, nr.1] using hshape⟩

end Readers5020
