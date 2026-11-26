"""Build a compact certificate for the 54-gate star-cover witness."""
from itertools import combinations
from pathlib import Path
import runpy

scratch = Path(__file__).resolve().parent
search = runpy.run_path(str(scratch / "search-9791.py"))
neighbors = search["NEIGHBORS"]
edges = [(a, b) for b, points in sorted(neighbors.items()) for a in points]
gates = []


def add(op, a, b):
    gates.append((op, a, b))
    return 23 + len(gates)


roots = [add("and", add("or", add("or", a, b), add("or", c, d)), j)
         for j, (a, b, c, d) in sorted(neighbors.items())]
out = roots[0]
for root in roots[1:]:
    out = add("or", out, root)
assert len(gates) == 54


def verify():
    """Use monotonicity and an independent maximal-negative generator."""
    assert len(edges) == 44
    assert all(len(hood) == 4 for hood in neighbors.values())
    assert all(len(set(first) & set(second)) == 1
               for first, second in combinations(neighbors.values(), 2))
    positives = [(1 << a) | (1 << b) for a, b in edges]
    negatives = []
    for flags in range(1 << 11):
        right = {13 + i for i in range(11) if flags >> i & 1}
        left = {a for a in range(13) if all((a, b) not in edges for b in right)}
        if all(b in right or any((a, b) in edges for a in left) for b in range(13, 24)):
            negatives.append(sum(1 << i for i in left | right))
    assert len(negatives) == 423
    for mask, want in [(m, True) for m in positives] + [(m, False) for m in negatives]:
        xs = [bool(mask >> i & 1) for i in range(24)]
        for op, a, b in gates:
            xs.append((xs[a] and xs[b]) if op == "and" else (xs[a] or xs[b]))
        assert xs[out] == want
    print(f"Verified {len(positives)} minimal positives and {len(negatives)} maximal negatives.")


verify()


def v(i):
    return f"x {i}" if i < 24 else f"v{i} x"


star = []
word = [f"x {i}" for i in range(24)]
stages = [
    "def ws0 (x : Fin 24 → Bool) : List Bool := [" + ", ".join(word) + "]",
    "theorem init (x : Fin 24 → Bool) : List.ofFn x = ws0 x := by rfl",
]
for op, a, b in gates:
    index = len(star) + 1
    i = 23 + index
    star.append(f"def v{i} (x : Fin 24 → Bool) := GateOp.eval .{op} [{v(a)}, {v(b)}]")
    word.append(f"v{i} x")
    stages.extend([
        f"def ws{index} (x : Fin 24 → Bool) : List Bool := [" + ", ".join(word) + "]",
        f"theorem stage{index} (x : Fin 24 → Bool) : "
        f"step (ws{index - 1} x) ⟨.{op}, [{a}, {b}]⟩ = ws{index} x := by rfl"
    ])
stars = "\n".join(star)
stage_defs = "\n".join(stages)
step_names = ", ".join(f"stage{i}" for i in range(1, 55))
wire_names = ", ".join(f"v{i}" for i in range(24, 78))
plist = "[" + ", ".join(f"({a}, {b})" for a, b in edges) + "]"
gatelist = ",\n    ".join(f"⟨.{o}, [{a},{b}]⟩" for o, a, b in gates)
code = f"""import Mathlib
import PEqualNP.Defs

namespace Near9791

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edges : List (ℕ × ℕ) := {plist}

def witness : Circuit :=
  ⟨[{gatelist}], {out}⟩

{stars}

def step (xs : List Bool) (g : Gate) : List Bool :=
  xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)]

{stage_defs}

theorem orDistrib (a b c : Bool) : ((a || b) && c) = ((a && c) || (b && c)) := by
  cases a <;> cases b <;> cases c <;> rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
theorem eval_star (x : Fin 24 → Bool) :
    witness.eval (List.ofFn x) = v{out} x := by
  change ((witness.gates.foldl step (List.ofFn x)).getD {out} false) = _
  rw [init]
  simp only [witness, List.foldl_cons, List.foldl_nil, {step_names}]
  rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
theorem star_edges (x : Fin 24 → Bool) :
    v{out} x = edges.any (fun e => x (Fin.ofNat 24 e.1) && x (Fin.ofNat 24 e.2)) := by
  simp [{wire_names}, GateOp.eval, edges, orDistrib, Bool.or_assoc]
  rfl

set_option maxRecDepth 20000 in
theorem witness54 :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 54 ∧ ∀ x : Fin 24 → Bool,
      (C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin 24, (u.val, v.val) ∈ edges ∧ x u = true ∧ x v = true) := by
  have monotone : Monotone2 witness := by
    intro g hg
    simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with {" | ".join("rfl" for _ in gates)} <;> first
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
"""
(scratch / "Near9791.lean").write_text(code, encoding="utf-8", newline="\n")
