import Mathlib

namespace SpectralProjGrad.Shared

/-- The nonmonotone reference value of iteration `k` (0-based):
`max_{0 ≤ j ≤ min {k, M-1}} f(x_{k-j})`, the largest objective value among the last
`min {k, M-1} + 1` iterates `x_k, x_{k-1}, …`. -/
noncomputable def nonmonotoneRef {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (M k : ℕ) : ℝ :=
  (Finset.range (min k (M - 1) + 1)).sup' Finset.nonempty_range_add_one
    (fun j => f (x (k - j)))

end SpectralProjGrad.Shared
