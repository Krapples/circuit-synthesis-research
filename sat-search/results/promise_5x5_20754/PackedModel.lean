import Mathlib.Data.List.Perm.Basic

namespace ActiveBudget20754

abbrev Table := BitVec 12
abbrev Wire := BitVec 4

def inputs : List Table := [0, 4095, 15, 240, 3840, 273, 546, 1092, 2184]

def read : List Table → Wire → Table
  | [], _ => 0
  | v :: vs, i => if i == 0 then v else read vs (i - 1)

def gate (w : List Table) (isOr : Bool) (a b : Wire) : Table :=
  if isOr then read w a ||| read w b else read w a &&& read w b

end ActiveBudget20754
