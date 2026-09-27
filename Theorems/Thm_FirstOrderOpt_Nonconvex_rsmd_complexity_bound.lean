import Mathlib

namespace FirstOrderOpt.Nonconvex

open scoped RealInnerProductSpace
open MeasureTheory

/-- Theorem 6.6(a) (RSMD complexity bound) — the goal theorem. `Ψ := f + h` on closed convex `X`,
`f` has `L`-Lipschitz gradient `fGrad`. `x k`, `G k` (the batch-averaged stochastic gradient at
step `k`), `xPlus k` (the generalized projection (6.2.6) at `x k` using `G k`) are random
variables on a probability space `(Ω, P)`, adapted to a filtration `𝒢` representing the history
`ξ[k-1]` (`x k`, `G k` are `𝒢 (k-1)`-measurable, matching "`x_k` is a function of the history
`ξ[k-1]`"); `x (k+1) = xPlus k` and `gXtilde k := (1/γ k)•(x k - xPlus k)` is the stochastic
projected gradient `P_X(x k, G k, γ k)` (6.2.32). Assumption 13 is stated conditionally on the
history, matching the book's own `E[⟨δ_k,g_{X,k}⟩ | ξ[k-1]] = 0`: `δ k := G k - fGrad (x k)` has
conditional mean `0` and conditional second moment `≤ σ²/m k` given `𝒢 (k-1)` (the `σ²/m k` bound
is (6.2.40)'s conclusion for the `m k`-sample batch average, taken here directly as the
hypothesis on `G k` rather than re-derived from `m k` raw i.i.d. calls). `R : Ω → ℕ` is a random
stopping index, independent of every `gXtilde k`, supported on `{1,…,N}` with the pmf `PR` of
(6.2.30). Then `E[‖gXtilde_R‖²] ≤ (L·DΨ² + σ²Σ_{k=1}^N(γ k/m k)) / Σ_{k=1}^N(γ k - Lγ k²)`. -/
theorem rsmd_complexity_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {Ω : Type*} {m0 : MeasurableSpace Ω} (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] (𝒢 : MeasureTheory.Filtration ℕ m0)
    (X : Set E) (f h : E → ℝ) (V : E → E → ℝ) (L σ : ℝ) (hL : 0 < L) (hσ : 0 ≤ σ)
    (fGrad : E → E)
    (hSmooth : ∀ x ∈ X, ∀ y ∈ X, f y - f x - ⟪fGrad x, y - x⟫ ≤ (L / 2) * ‖y - x‖ ^ 2)
    (N : ℕ) (hN : 1 ≤ N)
    (x1 : E) (hx1 : x1 ∈ X)
    (x G xPlus gXtilde : ℕ → Ω → E) (γ mBatch : ℕ → ℝ)
    (hmBatch : ∀ k, 1 ≤ k → k ≤ N → 0 < mBatch k)
    (hx1def : ∀ ω, x 1 ω = x1)
    (hxMeas : ∀ k, 1 ≤ k → StronglyMeasurable[𝒢 (k - 1)] (x k))
    (hGMeas : ∀ k, 1 ≤ k → StronglyMeasurable[𝒢 (k - 1)] (G k))
    (hx : ∀ k, ∀ ω, x k ω ∈ X) (hxPlusMem : ∀ k, ∀ ω, xPlus k ω ∈ X)
    (hxPlusDef : ∀ k, 1 ≤ k → k ≤ N → ∀ ω, ∀ u ∈ X,
      ⟪G k ω, xPlus k ω⟫ + (1 / γ k) * V (x k ω) (xPlus k ω) + h (xPlus k ω) ≤
        ⟪G k ω, u⟫ + (1 / γ k) * V (x k ω) u + h u)
    (hxNext : ∀ k, 1 ≤ k → k ≤ N → ∀ ω, x (k + 1) ω = xPlus k ω)
    (hgXtilde : ∀ k, 1 ≤ k → k ≤ N → ∀ ω, gXtilde k ω = (1 / γ k) • (x k ω - xPlus k ω))
    (hγpos : ∀ k, 1 ≤ k → k ≤ N → 0 < γ k) (hγub : ∀ k, 1 ≤ k → k ≤ N → γ k ≤ 1 / L)
    (hγstrict : ∃ k, 1 ≤ k ∧ k ≤ N ∧ γ k < 1 / L)
    (hDeltaInt : ∀ k, 1 ≤ k → k ≤ N →
      MeasureTheory.Integrable (fun ω => G k ω - fGrad (x k ω)) P)
    (hDeltaSqInt : ∀ k, 1 ≤ k → k ≤ N →
      MeasureTheory.Integrable (fun ω => ‖G k ω - fGrad (x k ω)‖ ^ 2) P)
    (hUnbiased : ∀ k, 1 ≤ k → k ≤ N →
      MeasureTheory.condExp (𝒢 (k - 1)) P (fun ω => G k ω - fGrad (x k ω)) =ᵐ[P] 0)
    (hVariance : ∀ k, 1 ≤ k → k ≤ N →
      MeasureTheory.condExp (𝒢 (k - 1)) P (fun ω => ‖G k ω - fGrad (x k ω)‖ ^ 2) ≤ᵐ[P]
        (fun _ => σ ^ 2 / mBatch k))
    (ΨStar : ℝ) (hΨStar : IsGLB ((fun x => f x + h x) '' X) ΨStar)
    (DΨ : ℝ) (hDΨ : DΨ = Real.sqrt ((f x1 + h x1 - ΨStar) / L))
    (R : Ω → ℕ) (hRmeas : Measurable R) (hRsupp : ∀ ω, 1 ≤ R ω ∧ R ω ≤ N)
    (PR : ℕ → ℝ)
    (hPR : ∀ k, 1 ≤ k → k ≤ N →
      PR k = (γ k - L * (γ k) ^ 2) / ∑ j ∈ Finset.Icc 1 N, (γ j - L * (γ j) ^ 2))
    (hRlaw : ∀ k, 1 ≤ k → k ≤ N → P {ω | R ω = k} = ENNReal.ofReal (PR k))
    (hRindep : ∀ k, 1 ≤ k → k ≤ N → ProbabilityTheory.IndepFun R (gXtilde k) P)
    (gXtildeR : Ω → E) (hgXtildeR : ∀ ω, gXtildeR ω = gXtilde (R ω) ω)
    (hgXtildeRInt : MeasureTheory.Integrable (fun ω => ‖gXtildeR ω‖ ^ 2) P) :
    ∫ ω, ‖gXtildeR ω‖ ^ 2 ∂P ≤
      (L * DΨ ^ 2 + σ ^ 2 * ∑ k ∈ Finset.Icc 1 N, (γ k / mBatch k)) /
        ∑ k ∈ Finset.Icc 1 N, (γ k - L * (γ k) ^ 2) := by sorry

end FirstOrderOpt.Nonconvex

