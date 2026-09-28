import Mathlib

namespace HighDimStat.Pca

/-- The `ℓ2`-operator norm `|||A|||₂` of a *symmetric* `d × d` real matrix `A`, realized via its
Rayleigh-quotient variational characterization `sup_{‖v‖₂=1} |⟨v, Av⟩|`, as used for the
perturbation matrix `P` throughout Wainwright, *High-Dimensional Statistics* (2019), Section 8.2
(e.g. Eq. (8.9), Theorem 8.5). For a symmetric matrix this coincides with the largest singular
value / largest eigenvalue magnitude, the book's own `|||·|||₂`. -/
noncomputable def opNormSymm {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ⨆ v : {v : Fin d → ℝ // ∑ j, (v j) ^ 2 = 1}, |∑ i, v.1 i * (A.mulVec v.1) i|

end HighDimStat.Pca
