import Mathlib

namespace TSPHeuristics.NNLower

/-- `WalkCost E x y c`: in the undirected weighted (multi)graph whose edges are the triples
`(a, b, w) ∈ E` (an edge between nodes `a` and `b` of weight `w`), there is a walk from `x` to `y`
of total weight `c`. The empty walk from `x` to `x` has weight `0`; an edge may be traversed in
either direction. -/
inductive WalkCost (E : List (ℕ × ℕ × ℝ)) : ℕ → ℕ → ℝ → Prop
  | nil (x : ℕ) : WalkCost E x x 0
  | cons {x y z : ℕ} {w c : ℝ} (he : (x, y, w) ∈ E ∨ (y, x, w) ∈ E) (h : WalkCost E y z c) :
      WalkCost E x z (w + c)

/-- The shortest-path distance between `x` and `y` in the weighted graph `E`: the infimum of the
weights of all walks from `x` to `y`. For nonnegative weights and `x`, `y` in the same connected
component this is the length of a minimal path. (If no walk exists the set is empty and the real
`sInf` is `0`; the graphs this is applied to are connected.) -/
noncomputable def spDist (E : List (ℕ × ℕ × ℝ)) (x y : ℕ) : ℝ :=
  sInf {c : ℝ | WalkCost E x y c}

end TSPHeuristics.NNLower
