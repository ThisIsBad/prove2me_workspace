import Mathlib

open MeasureTheory

namespace SupplyChainFactoring.Choice

/-- Complementary CDF `F̄(x) = P(D > x) = 1 − F(x)` of the demand law `μ` (Kouvelis–Xu 2021, §3.1,
p. 6075). -/
noncomputable def Fbar (μ : Measure ℝ) (x : ℝ) : ℝ := (μ (Set.Ioi x)).toReal

/-- Expected sales `S(q) = E[min(D, q)] = ∫₀^q F̄(ξ) dξ` (p. 6076). -/
noncomputable def S (μ : Measure ℝ) (q : ℝ) : ℝ := ∫ ξ in (0 : ℝ)..q, Fbar μ ξ

/-- `k(q) = S(q) / F̄(q)` (p. 6076). -/
noncomputable def k (μ : Measure ℝ) (q : ℝ) : ℝ := S μ q / Fbar μ q

/-- Failure rate `z(ξ) = f(ξ) / F̄(ξ)` of the demand with density `f` (p. 6075). -/
noncomputable def z (μ : Measure ℝ) (f : ℝ → ℝ) (ξ : ℝ) : ℝ := f ξ / Fbar μ ξ

/-- The demand assumptions of §3.1 (p. 6075): the demand `D` is a nonnegative random variable with
law `μ` and probability density `f`; (i) it has a finite mean and a continuous p.d.f. with
`f(ξ) > 0` on `[0, Z]` (`Z ≤ +∞`), `Z` being the upper end of the support; (ii) its failure rate
`z(ξ) = f(ξ)/F̄(ξ)` is strictly increasing (strict IFR). Continuity of `f` is read on the support
`[0, Z]` (a density that vanishes after a finite `Z` cannot be continuous on all of `ℝ`). -/
structure DemandModel (μ : Measure ℝ) (f : ℝ → ℝ) (Z : EReal) : Prop where
  isProbability : IsProbabilityMeasure μ
  f_nonneg : ∀ x, 0 ≤ f x
  hasDensity : μ = volume.withDensity (fun x => ENNReal.ofReal (f x))
  nonneg : μ (Set.Iio 0) = 0
  finiteMean : Integrable (fun x : ℝ => x) μ
  Z_pos : 0 < Z
  support_le : ∀ x : ℝ, Z ≤ (x : EReal) → μ (Set.Ioi x) = 0
  f_continuousOn : ContinuousOn f {x : ℝ | 0 ≤ x ∧ (x : EReal) ≤ Z}
  f_pos : ∀ x : ℝ, 0 ≤ x → (x : EReal) ≤ Z → 0 < f x
  strictIFR : StrictMonoOn (z μ f) {x : ℝ | 0 ≤ x ∧ (x : EReal) < Z}

end SupplyChainFactoring.Choice
