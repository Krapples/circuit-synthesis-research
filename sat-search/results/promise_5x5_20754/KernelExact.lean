import ExactModel
import TraceDemand

namespace ActiveBudget20754

open PEqualNP.Represents
open Promise20754 (Rule CorrectTrace available bases liveInputs no_seven_rule_trace)

private theorem lookup_membership (w : List Table) (i : Wire) :
    read w i ∈ w ∨ read w i = 0 := by
  rw [read_eq, List.getD_eq_getElem?_getD]
  cases h : w[i.toNat]? with
  | none => exact Or.inr rfl
  | some t =>
    exact Or.inl (List.mem_of_getElem? h)

private theorem inputs_available (rs : List Rule) : inputs ⊆ available rs := by
  intro t ht
  apply List.mem_append_right
  have hp : inputs.Perm bases := by
    change ([0, 4095] ++ liveInputs).Perm (liveInputs ++ [0, 4095])
    exact List.perm_append_comm
  exact hp.mem_iff.mp ht

private theorem read_available {w : List Table} {rules : List Rule}
    (old : w ⊆ available rules) (i : Wire) : read w i ∈ available rules := by
  rcases lookup_membership w i with hm | hz
  · exact old hm
  · rw [hz]
    exact inputs_available rules (by decide)

private theorem append_trace (recipes : List Recipe) (ts : List Table) (rules : List Rule)
    (good : CorrectTrace rules) (known : (inputs ++ ts) ⊆ available rules) :
    ∃ result, CorrectTrace result ∧ result.length ≤ rules.length + recipes.length ∧
      (inputs ++ run ts recipes) ⊆ available result := by
  induction recipes generalizing ts rules with
  | nil => exact ⟨rules, good, by simp, known⟩
  | cons rec rs ih =>
    let r : Rule := ⟨rec.isOr, read (inputs ++ ts) rec.a, read (inputs ++ ts) rec.b⟩
    have hl : r.left ∈ available rules := read_available known rec.a
    have hr : r.right ∈ available rules := read_available known rec.b
    change ∃ result, CorrectTrace result ∧ result.length ≤ rules.length + (rec :: rs).length ∧
      (inputs ++ run (ts ++ [r.result]) rs) ⊆ available result
    by_cases old : r.result ∈ available rules
    · have extended : (inputs ++ (ts ++ [r.result])) ⊆ available rules := by
        rw [← List.append_assoc]
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact known hx
        · rwa [List.mem_singleton.mp hx]
      obtain ⟨result, hc, hb, hv⟩ := ih (ts ++ [r.result]) rules good extended
      exact ⟨result, hc, by simp only [List.length_cons]; omega, hv⟩
    · have extended : (inputs ++ (ts ++ [r.result])) ⊆ available (r :: rules) := by
        rw [← List.append_assoc]
        intro x hx
        change x ∈ r.result :: available rules
        rcases List.mem_append.mp hx with hx | hx
        · exact List.mem_cons_of_mem _ (known hx)
        · exact List.mem_cons.mpr (Or.inl (List.mem_singleton.mp hx))
      obtain ⟨result, hc, hb, hv⟩ :=
        ih (ts ++ [r.result]) (r :: rules) (.add r rules good hl hr old) extended
      exact ⟨result, hc, by simp only [List.length_cons] at *; omega, hv⟩

theorem kernel_not_rep_size_at_most_seven :
    ¬ RepSizeAtMost (fun u v : Fin 5 => (12815360 : ℕ).testBit (5 * u.val + v.val)) 7 := by
  intro h
  obtain ⟨recipes, bound, o, _, output⟩ := project_to_packed h
  obtain ⟨rules, correct, size, known⟩ :=
    append_trace recipes [] [] .empty (by simpa using inputs_available [])
  have output_known := read_available known o
  rw [output] at output_known
  apply no_seven_rule_trace correct _ output_known
  simp only [List.length_nil, Nat.zero_add] at size
  omega

end ActiveBudget20754
