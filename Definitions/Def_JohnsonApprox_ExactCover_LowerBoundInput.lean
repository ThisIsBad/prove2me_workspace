import Mathlib
import Definitions.Def_JohnsonApprox_ExactCover_Problem

namespace JohnsonApprox.ExactCover

/-- The points are pairs `(s, r)`: segment `s ∈ {1, …, k}`, position `r ∈ {0, …, k! − 1}`.
`lbF0 k r` is the `r`-th set of `F₀`: one point `(s, r)` from each segment `s = 1, …, k`. -/
def lbF0 (k r : ℕ) : Finset (ℕ × ℕ) := (Finset.Icc 1 k).image (fun s => (s, r))

/-- `lbBlock k j q` is the `q`-th set of `F₁` covering segment `j` (`q < k!/j`): the `j` points
`(j, q·j), …, (j, q·j + j − 1)` of segment `j`, filled out with the `k − j` points
`(k, 0), …, (k, k − j − 1)` of segment `k`, so that it has exactly `k` elements. -/
def lbBlock (k j q : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range j).image (fun t => (j, q * j + t)) ∪ (Finset.range (k - j)).image (fun t => (k, t))

/-- The family `F₀ ++ F₁`: the `k!` sets of `F₀`, then for `j = 1, …, k` the `k!/j` sets of `F₁`
covering segment `j`. -/
def lbSets (k : ℕ) : List (Finset (ℕ × ℕ)) :=
  (List.range k.factorial).map (lbF0 k) ++
    (List.range' 1 k).flatMap (fun j => (List.range (k.factorial / j)).map (lbBlock k j))

/-- The lower-bound input of Theorem 6 (Fig. 1 with every set of `F₁` filled out from segment `k`
to exactly `k` elements), as an EC input indexed by positions in `lbSets k`. -/
def lbInput (k : ℕ) : Input (ℕ × ℕ) := ⟨(lbSets k).length, fun i => (lbSets k).get i⟩

end JohnsonApprox.ExactCover
