import Mathlib

namespace FoundationsML.Boosting

/-- The `ρ`-margin loss function `Φ_ρ` (Mohri, Rostamizadeh & Talwalkar, *Foundations of
Machine Learning*, 2nd ed., MIT Press 2018, Definition 5.5, p. 92, PDF p. 109, restated locally
for this chapter since drafts cannot import another chunk's draft module):
`Φ_ρ(x) = min(1, max(0, 1 − x/ρ))`. -/
noncomputable def PhiRho (ρ : ℝ) (x : ℝ) : ℝ := min 1 (max 0 (1 - x / ρ))

end FoundationsML.Boosting
