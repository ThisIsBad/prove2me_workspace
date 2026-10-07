import Mathlib
import Definitions.Def_StochasticOrders_Multivariate_MultivariateOrder_v2


namespace StochasticOrders.Multivariate

open MeasureTheory ProbabilityTheory

/-- Theorem 6.B.16(b) (Shaked & Shanthikumar, *Stochastic Orders*, Springer 2007, p. 273): let
`X 1, …, X m` be independent random vectors, `X i` of dimension `k i`, and `Y 1, …, Y m` another
independent family with `Y i` of dimension `k i`. If `X i ≤st Y i` for every `i`, then for any
increasing function `ψ : ℝ^k → ℝ` (`k = k 1 + ⋯ + k m`, the concatenated vector living in
`(i : Fin m) → Fin (k i) → ℝ` with its coordinatewise order), `ψ(X 1, …, X m) ≤st ψ(Y 1, …, Y m)`
in the *univariate* usual stochastic order (`ψ` has codomain `ℝ`), stated directly as the
univariate order's defining inequality since drafts cannot import another mission's `UsualOrder`.

Corrected version (`_v2`) of `multivariate_order_conjunction`: (1) `ψ` is Borel measurable, as
the book's "`ψ(X)` is a random variable" requires — an increasing function on `ℝ^k`, `k ≥ 2`,
need not be Borel, and for a non-Borel `ψ` the outer measure `μ {x < ψ ∘ X}` is not determined by
the law of `X`, which is how the retired statement was refuted. (2) `MultivariateOrder` is the
corrected `_v2` definition (Borel test functions). (3) The book's general dimensions `k i` are
kept rather than a common dimension `n`. -/
theorem multivariate_order_conjunction_v2 {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {m : ℕ} (k : Fin m → ℕ) (X : (i : Fin m) → Ω → Fin (k i) → ℝ)
    (Y : (i : Fin m) → Ω' → Fin (k i) → ℝ)
    (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    (hXindep : iIndepFun X μ) (hYindep : iIndepFun Y ν)
    (hord : ∀ i, MultivariateOrder μ ν (X i) (Y i))
    (ψ : ((i : Fin m) → Fin (k i) → ℝ) → ℝ) (hψmeas : Measurable ψ) (hψ : Monotone ψ) :
    ∀ x : ℝ, μ {ω | x < ψ (fun i => X i ω)} ≤ ν {ω | x < ψ (fun i => Y i ω)} := by sorry

end StochasticOrders.Multivariate

