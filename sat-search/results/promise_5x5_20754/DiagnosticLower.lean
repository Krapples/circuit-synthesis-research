import ActiveBudget
import ExactModel

namespace ActiveBudget20754

open PEqualNP.Represents

private theorem diagnosticAppendLookup {α : Type} (xs ys : List α) (d : α) (i : ℕ) :
    (xs ++ ys).getD i d =
      if i < xs.length then xs.getD i d else ys.getD (i - xs.length) d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append]
  split <;> rfl

private theorem run_append (ts : List Table) (rs ss : List Recipe) :
    run ts (rs ++ ss) = run (run ts rs) ss := List.foldl_append

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
  rwa [run_append, hu, ← List.append_assoc, read_eq, diagnosticAppendLookup, ite_eq_left ho, ← read_eq] at hp

theorem not_rep_size_at_most_seven : ¬ RepSizeAtMost target 7 := by
  intro h
  obtain ⟨rs, hlen, o, ho, hvalue⟩ := project_to_packed h
  exact packed_at_most rs hlen o ho hvalue

end ActiveBudget20754
