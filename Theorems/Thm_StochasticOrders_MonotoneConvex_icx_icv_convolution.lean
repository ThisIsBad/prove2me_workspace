import Mathlib
import Definitions.Def_StochasticOrders_MonotoneConvex_IcxOrder
import Definitions.Def_StochasticOrders_MonotoneConvex_IcvOrder

namespace StochasticOrders.MonotoneConvex

open MeasureTheory ProbabilityTheory

/-- Theorem 4.A.8(d) (Shaked & Shanthikumar, *Stochastic Orders*, Springer 2007, p. 186): let
`X₁, …, Xₘ` be independent random variables and `Y₁, …, Yₘ` another independent family. If
`Xᵢ ≤icx Yᵢ` for every `i`, then `∑ᵢ Xᵢ ≤icx ∑ᵢ Yᵢ`; and if `Xᵢ ≤icv Yᵢ` for every `i`, then
`∑ᵢ Xᵢ ≤icv ∑ᵢ Yᵢ`: both the increasing convex and increasing concave orders are closed under
convolutions. -/
theorem icx_icv_convolution {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {m : ℕ} (X : Fin m → Ω → ℝ) (Y : Fin m → Ω' → ℝ) (hX : ∀ i, Measurable (X i))
    (hY : ∀ i, Measurable (Y i)) (hXindep : iIndepFun X μ) (hYindep : iIndepFun Y ν) :
    ((∀ i, IcxOrder μ ν (X i) (Y i)) →
      IcxOrder μ ν (fun ω => ∑ i, X i ω) (fun ω => ∑ i, Y i ω))
    ∧
    ((∀ i, IcvOrder μ ν (X i) (Y i)) →
      IcvOrder μ ν (fun ω => ∑ i, X i ω) (fun ω => ∑ i, Y i ω)) := by sorry

end StochasticOrders.MonotoneConvex
