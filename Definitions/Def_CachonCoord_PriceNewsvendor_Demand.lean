import Mathlib

namespace CachonCoord.PriceNewsvendor

/-- The distribution function of a real-valued demand law. -/
noncomputable def cdfOf (ν : MeasureTheory.Measure ℝ) (y : ℝ) : ℝ :=
  (ν (Set.Iic y)).toReal

/-- Price-indexed, nonnegative demand in §6.3. Prices are chosen from a nonempty open set.
The price derivative records the chapter's stochastic decrease of demand as price rises. -/
structure DemandFamily where
  prices : Set ℝ
  prices_nonempty : prices.Nonempty
  prices_open : IsOpen prices
  law : ℝ → MeasureTheory.Measure ℝ
  probability : ∀ p ∈ prices, MeasureTheory.IsProbabilityMeasure (law p)
  nonnegative : ∀ p ∈ prices, law p (Set.Iio 0) = 0
  no_zero_mass : ∀ p ∈ prices, law p ({0} : Set ℝ) = 0
  finite_mean : ∀ p ∈ prices, MeasureTheory.Integrable (fun d : ℝ => d) (law p)
  cdf_strict : ∀ p ∈ prices, StrictMonoOn (cdfOf (law p)) (Set.Ici 0)
  cdf_differentiable : ∀ p ∈ prices, ∀ y : ℝ, 0 < y →
    DifferentiableAt ℝ (cdfOf (law p)) y
  priceSlope : ℝ → ℝ → ℝ
  price_derivative : ∀ p ∈ prices, ∀ y : ℝ, 0 < y →
    HasDerivAt (fun t => cdfOf (law t) y) (priceSlope y p) p
  price_slope_pos : ∀ p ∈ prices, ∀ y : ℝ, 0 < y → 0 < priceSlope y p

end CachonCoord.PriceNewsvendor
