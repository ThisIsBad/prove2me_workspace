import Mathlib
import Definitions.Def_KWSpectrum_Estimator_Model

namespace KWSpectrum.Estimator

open QAlgorithms QAlgorithms.Schur

/-- Keyl–Werner, arXiv:quant-ph/0102027v1, p. 4: the rate function (13) is the Legendre
transform of `c(η) = ln Σ_α r_α e^{η_α}`: `I(s) = sup_{η ∈ ℝ^d} (η · s − c(η))` for `r, s ∈ Σ`,
in `[0, ∞]`. -/
theorem legendre {d : ℕ} (r s : Fin d → ℝ) (hr : r ∈ SpectrumSet d) (hs : s ∈ SpectrumSet d) :
    rate r s = ⨆ η : Fin d → ℝ,
      (((∑ j : Fin d, η j * s j) - Real.log (∑ α : Fin d, r α * Real.exp (η α)) : ℝ) : EReal) := by sorry

end KWSpectrum.Estimator

