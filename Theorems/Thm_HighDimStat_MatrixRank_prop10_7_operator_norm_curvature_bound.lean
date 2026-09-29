import Mathlib
import Definitions.Def_HighDimStat_MatrixRank_Core

namespace HighDimStat.MatrixRank

/-- Proposition 10.7 (p. 321): suppose the observation operator `Xn` satisfies the `Φ*`-
curvature condition (10.20) with parameter `κ > 0`, and consider a matrix `Θ*` with
`rank(Θ*) < κ/(64τn)`. Then, conditioned on the event `G(λn) = {|||(1/n)X*ₙ(w)|||₂ ≤ λn/2}`,
any optimal solution to the M-estimator (10.16) satisfies the operator-norm bound
`|||Θ̂ − Θ*|||₂ ≤ 3√2 λn/κ`. -/
theorem prop10_7_operator_norm_curvature_bound {d1 d2 n : ℕ}
    (Xs : Fin n → Matrix (Fin d1) (Fin d2) ℝ) (w : Fin n → ℝ)
    (Θstar Θhat : Matrix (Fin d1) (Fin d2) ℝ) (κ τn lamN : ℝ)
    (hκ : 0 < κ) (hτn : 0 ≤ τn) (hlam : 0 < lamN)
    (hcurv : DualCurvatureNuclear Xs κ τn)
    (hrank : (Θstar.rank : ℝ) < κ / (64 * τn))
    (hsol : IsNuclearNormLSSolution Xs (fun i => traceInner (Xs i) Θstar + w i) lamN Θhat)
    (hG : opNorm ((1 / (n : ℝ)) • observationOpAdjoint Xs w) ≤ lamN / 2) :
    opNorm (Θhat - Θstar) ≤ 3 * Real.sqrt 2 * lamN / κ := by sorry

end HighDimStat.MatrixRank
