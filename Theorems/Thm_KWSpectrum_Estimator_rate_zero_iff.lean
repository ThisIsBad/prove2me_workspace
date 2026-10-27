import Mathlib
import Definitions.Def_KWSpectrum_Estimator_Model

namespace KWSpectrum.Estimator

open QAlgorithms QAlgorithms.Schur

/-- Keyl–Werner, arXiv:quant-ph/0102027v1, p. 3 (after eq. (11)), with eq. (13): the rate
function is nonnegative on `Σ` and vanishes only at `s = r`. -/
theorem rate_zero_iff {d : ℕ} (r s : Fin d → ℝ) (hr : r ∈ SpectrumSet d)
    (hs : s ∈ SpectrumSet d) :
    0 ≤ rate r s ∧ (rate r s = 0 ↔ s = r) := by sorry

end KWSpectrum.Estimator

