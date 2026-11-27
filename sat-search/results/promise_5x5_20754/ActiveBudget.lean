import Mathlib

namespace ActiveBudget20754

abbrev Table := BitVec 12
abbrev Wire := BitVec 4

def inputs : List Table := [0, 4095, 15, 240, 3840, 273, 546, 1092, 2184]

def read : List Table → Wire → Table
  | [], _ => 0
  | v :: vs, i => if i == 0 then v else read vs (i - 1)

def gate (w : List Table) (isOr : Bool) (a b : Wire) : Table :=
  if isOr then read w a ||| read w b else read w a &&& read w b

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem no_packed_witness
    (a₀ b₀ a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ a₅ b₅ a₆ b₆ out : Wire)
    (o₀ o₁ o₂ o₃ o₄ o₅ o₆ : Bool)
    (w₀ w₁ w₂ w₃ w₄ w₅ w₆ : Table)
    (h₀ : w₀ = gate inputs o₀ a₀ b₀)
    (h₁ : w₁ = gate (inputs ++ [w₀]) o₁ a₁ b₁)
    (h₂ : w₂ = gate (inputs ++ [w₀,w₁]) o₂ a₂ b₂)
    (h₃ : w₃ = gate (inputs ++ [w₀,w₁,w₂]) o₃ a₃ b₃)
    (h₄ : w₄ = gate (inputs ++ [w₀,w₁,w₂,w₃]) o₄ a₄ b₄)
    (h₅ : w₅ = gate (inputs ++ [w₀,w₁,w₂,w₃,w₄]) o₅ a₅ b₅)
    (h₆ : w₆ = gate (inputs ++ [w₀,w₁,w₂,w₃,w₄,w₅]) o₆ a₆ b₆) :
    read (inputs ++ [w₀,w₁,w₂,w₃,w₄,w₅,w₆]) out ≠ 3187 := by
  simp only [inputs, gate, List.cons_append, List.nil_append, read] at h₀ h₁ h₂ h₃ h₄ h₅ h₆ ⊢
  bv_decide (config := { timeout := 35 })

end ActiveBudget20754
