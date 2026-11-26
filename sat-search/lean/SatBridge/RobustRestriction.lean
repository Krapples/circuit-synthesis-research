import SatBridge.SixQ
import CircuitLemmas.BlockProduct

namespace SatBridge

open PEqualNP.Search CircuitLemmas.GateElim

/-- Transfer the equal-width pair-sensitive block bound to external SAT at lengths divisible by six.
The coordinate restriction is supplied by `hword`; the fixed coordinates must account for the
complement of the free blocks in the length identity `hsize`. -/
theorem sat_robust_restriction_lower {Q k r d : ℕ} (hQ : 1 ≤ Q) (hk : 0 < k)
    (hd : 2 ≤ d) (hdr : d ≤ r) (D : PEqualNP.CircuitLowerBounds.Circuit)
    (hD : ∀ g ∈ D.gates, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} :
        Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2)
    (hdec : D.Decides SAT (6 * (Q + 1))) (V : ℕ → Finset ℕ)
    (φ : ℕ → (ℕ → Bool) → Bool) (F : Finset ℕ) (b : ℕ → Bool)
    (hVn : ∀ j < k, ∀ w ∈ V j, w < 6 * (Q + 1))
    (hdisj : ∀ i < k, ∀ j < k, i ≠ j → Disjoint (V i) (V j))
    (hdep : ∀ j < k, DepOn (V j) (φ j)) (hps : ∀ j < k, PS d (V j) (φ j))
    (hcard : ∀ j < k, (V j).card = r) (hFn : ∀ z ∈ F, z < 6 * (Q + 1))
    (hsize : F.card + k * r = 6 * (Q + 1))
    (hword : ∀ x, (List.ofFn fun i : Fin (6 * (Q + 1)) => fixS F b x i) ∈ SAT ↔
      prodP k φ x = true) :
    6 * (Q + 1) + k * (2 * r + 3 - 3 * d) ≤ D.size := by
  have hres : ∀ x, D.eval (List.ofFn fun i : Fin (6 * (Q + 1)) => fixS F b x i) =
      prodP k φ x := by
    intro x
    apply Bool.eq_iff_iff.2
    rw [hdec _ List.length_ofFn, hword]
  have hlower := block_restriction_lower hd hVn hdisj hdep hps
    (fun j hj => by rw [hcard j hj]; exact hdr) hk F b hFn
    (fun z hz => essential_of_L037 Q hQ D hdec z (hFn z hz)) hres (transfer _ D hD)
  have hsum : (Finset.range k).sum (fun j => (V j).card + 1 - d) = k * (r + 1 - d) := by
    calc
      _ = (Finset.range k).sum (fun _ => r + 1 - d) :=
        Finset.sum_congr rfl (fun j hj => by rw [hcard j (Finset.mem_range.mp hj)])
      _ = _ := by simp
  rw [hsum] at hlower
  by_cases hcoef : 3 * d ≤ 2 * r + 3
  · have he : r + (2 * r + 3 - 3 * d) = 3 * (r + 1 - d) := by omega
    have he' := congrArg (k * ·) he
    change k * (r + (2 * r + 3 - 3 * d)) = k * (3 * (r + 1 - d)) at he'
    rw [Nat.mul_add, ← Nat.mul_assoc k 3, Nat.mul_comm k 3, Nat.mul_assoc] at he'
    omega
  · have hz : 2 * r + 3 - 3 * d = 0 := by omega
    -- The block bound alone can have a negative excess. Full support gives the baseline
    -- via the previously checked six-bit theorem.
    have hbase := sat_six_lower Q hQ D hD hdec
    simp only [hz, Nat.mul_zero, Nat.add_zero]
    omega

end SatBridge
