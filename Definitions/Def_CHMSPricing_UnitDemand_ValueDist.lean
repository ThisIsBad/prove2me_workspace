import Mathlib

namespace CHMSPricing.UnitDemand

open MeasureTheory

/-- A value distribution with density `f`, measurable and strictly positive on the bounded
interval `[lo, hi]` (`0 ≤ lo < hi`), integrating to `1` there and putting no mass outside
(standing pin P1 for "distribution function `F` with density `f`", §2.1, p. 4). -/
structure ValueDist where
  lo : ℝ
  hi : ℝ
  f : ℝ → ℝ
  lo_nonneg : 0 ≤ lo
  lo_lt_hi : lo < hi
  f_measurable : Measurable f
  f_pos : ∀ x ∈ Set.Icc lo hi, 0 < f x
  f_intervalIntegrable : IntervalIntegrable f volume lo hi
  f_integral : ∫ x in lo..hi, f x = 1

namespace ValueDist

/-- The law of the value: density `f` on `[lo, hi]`, no mass outside. -/
noncomputable def law (D : ValueDist) : Measure ℝ :=
  (volume.restrict (Set.Icc D.lo D.hi)).withDensity (fun x => ENNReal.ofReal (D.f x))

/-- The distribution function `F(x) = Pr[v ≤ x]`. -/
noncomputable def cdf (D : ValueDist) (x : ℝ) : ℝ := (D.law (Set.Iic x)).toReal

/-- Definition 1 (p. 12): the virtual valuation `φ(v) = v − (1 − F(v)) / f(v)`. -/
noncomputable def virtualValue (D : ValueDist) (x : ℝ) : ℝ := x - (1 - D.cdf x) / D.f x

/-- Definition 2 (p. 12): `F` is regular if `φ` is monotone non-decreasing (on the support). -/
def Regular (D : ValueDist) : Prop := MonotoneOn D.virtualValue (Set.Icc D.lo D.hi)

end ValueDist

/-- The type space `∏ᵢ [loᵢ, hiᵢ]` of value profiles. -/
def typeSpace {ι : Type*} (D : ι → ValueDist) : Set (ι → ℝ) :=
  Set.pi Set.univ (fun i => Set.Icc (D i).lo (D i).hi)

/-- The common prior: the values `vᵢ ∼ Fᵢ` are drawn independently (product measure). -/
noncomputable def prior {ι : Type*} [Fintype ι] (D : ι → ValueDist) : Measure (ι → ℝ) :=
  Measure.pi (fun i => (D i).law)

end CHMSPricing.UnitDemand
