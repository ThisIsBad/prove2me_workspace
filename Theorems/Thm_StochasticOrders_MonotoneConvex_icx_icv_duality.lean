import Mathlib
import Definitions.Def_StochasticOrders_MonotoneConvex_IcxOrder
import Definitions.Def_StochasticOrders_MonotoneConvex_IcvOrder

namespace StochasticOrders.MonotoneConvex

open MeasureTheory

/-- Theorem 4.A.1 (Shaked & Shanthikumar, *Stochastic Orders*, Springer 2007, p. 182): let `X` and
`Y` be two random variables. Then `X ≤icx Y ⟺ −X ≥icv −Y` and `X ≤icv Y ⟺ −X ≥icx −Y`. The "≥"
direction is unfolded as the reversed order on the negated variables: `−X ≥icv −Y` means
`−Y ≤icv −X`, and likewise for the second equivalence. -/
theorem icx_icv_duality {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') (X : Ω → ℝ) (Y : Ω' → ℝ) :
    (IcxOrder μ ν X Y ↔ IcvOrder ν μ (fun ω => -(Y ω)) (fun ω => -(X ω))) ∧
    (IcvOrder μ ν X Y ↔ IcxOrder ν μ (fun ω => -(Y ω)) (fun ω => -(X ω))) := by sorry

end StochasticOrders.MonotoneConvex
