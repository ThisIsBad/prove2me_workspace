import Mathlib
import Definitions.Def_RetailVariety_Statics_Model
import Definitions.Def_RetailVariety_Structure_Model

namespace RetailVariety.Fashion

open ProbabilityTheory

/-- The critical fractile `z = Φ⁻¹(1 − c/p)` of (6), p. 1502, with `Φ` the standard normal c.d.f.
Mathlib has no normal quantile, so `z` is the least `x` with `1 − c/p ≤ Φ(x)`; for `0 < c < p` this
is the unique `x` with `Φ(x) = 1 − c/p`. -/
noncomputable def zCrit (p c : ℝ) : ℝ :=
  sInf {x : ℝ | 1 - c / p ≤ cdf (gaussianReal 0 1) x}

/-- The safety-stock coefficient `p σ λ^β e^{−z²/2} / √(2π)` of (7), p. 1502. -/
noncomputable def safetyCoeff (p c lam σ β : ℝ) : ℝ :=
  p * σ * lam ^ β * Real.exp (-(zCrit p c) ^ 2 / 2) / Real.sqrt (2 * Real.pi)

/-- The optimal expected profit (7), p. 1502, of the independent population model:
`π_I(S, v) = (p − c)λ ∑_{j∈S} q_j − (pσλ^β e^{−z²/2}/√(2π)) ∑_{j∈S} q_j^β`,
with `q_j^β` the real power `Real.rpow`. -/
noncomputable def profitI (p c lam σ β : ℝ) {n : ℕ} (v : Fin n → ℝ) (v0 : ℝ)
    (S : Finset (Fin n)) : ℝ :=
  (p - c) * lam * ∑ j ∈ S, RetailVariety.Structure.share v v0 S j
    - safetyCoeff p c lam σ β * ∑ j ∈ S, RetailVariety.Structure.share v v0 S j ^ β

/-- The optimal expected profit (8), p. 1502, of the trend-following population model:
`π_T(S, v) = ∑_{j∈S} (p q_j − c)^+ λ`. -/
noncomputable def profitT (p c lam : ℝ) {n : ℕ} (v : Fin n → ℝ) (v0 : ℝ)
    (S : Finset (Fin n)) : ℝ :=
  ∑ j ∈ S, max (p * RetailVariety.Structure.share v v0 S j - c) 0 * lam

end RetailVariety.Fashion
