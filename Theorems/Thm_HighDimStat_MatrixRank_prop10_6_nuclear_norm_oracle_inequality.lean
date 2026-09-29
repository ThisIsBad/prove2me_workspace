import Mathlib
import Definitions.Def_HighDimStat_MatrixRank_Core

namespace HighDimStat.MatrixRank

/-- Proposition 10.6 (p. 319): suppose the observation operator `Xn` satisfies the restricted
strong convexity condition (10.17) with parameter `κ > 0`. Then, conditioned on the good
event `G(λn) = {|||(1/n)Σwᵢ Xᵢ|||₂ ≤ λn/2}`, any optimal solution to nuclear-norm-regularized
least squares (10.16) satisfies the stated Frobenius-error bound, for any target rank
`r ∈ {1,...,d'}` with `r ≤ κn/(128 c0(d1+d2))`. -/
theorem prop10_6_nuclear_norm_oracle_inequality {d1 d2 n : ℕ}
    (Xs : Fin n → Matrix (Fin d1) (Fin d2) ℝ) (w : Fin n → ℝ)
    (Θstar Θhat : Matrix (Fin d1) (Fin d2) ℝ) (κ c0 lamN : ℝ) (r : ℕ)
    (hκ : 0 < κ) (hc0 : 0 ≤ c0) (hlam : 0 < lamN)
    (hRSC : RSCNuclear Xs κ c0)
    (hG : opNorm ((1 / (n : ℝ)) • observationOpAdjoint Xs w) ≤ lamN / 2)
    (hsol : IsNuclearNormLSSolution Xs (fun i => traceInner (Xs i) Θstar + w i) lamN Θhat)
    (hr1 : 1 ≤ r) (hr2 : r ≤ min d1 d2)
    (hr3 : (r : ℝ) ≤ κ * n / (128 * c0 * ((d1 : ℝ) + d2))) :
    (frobeniusNorm (Θhat - Θstar)) ^ 2 ≤
      9 / 2 * (lamN ^ 2 / κ ^ 2) * r +
        1 / κ * (2 * lamN * tailSingularSum Θstar r +
          32 * c0 * ((d1 : ℝ) + d2) / n * (tailSingularSum Θstar r) ^ 2) := by sorry

end HighDimStat.MatrixRank
