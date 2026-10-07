import Mathlib
import Definitions.Def_SmithRegenerative_CLT_CumulativeProcess

open MeasureTheory ProbabilityTheory Filter Topology

namespace SmithRegenerative.CLT

/-- Smith (1955), Theorem B, pp. 28–29 (Anscombe 1952, in Smith's form): "Let `ψ(t)` be an
unbounded, non-decreasing function of a real variable `t`. Let `m_t` be a proper random variable
taking positive integer values, and such that `m_t/ψ(t) → 1`, in probability. Let `{y_i}` be a
sequence of identically distributed, independent random variables, such that `Ey_i = 0`,
`var y_i = σ²` (5·4·1). Then, as `t → ∞`, `P{Σ₁^{m_t} y_i/(σ[ψ(t)]^{1/2}) ≤ α} → Φ(α)` (5·4·2)."

**Formalization Note** `σ > 0` is implicit in the paper (it divides by `σ`). No independence
between `m_t` and the `y_i` is assumed. `y 0` is unused; the sequence is `y 1, y 2, …`.
`Φ` is the distribution function of the standard normal law, `cdf (gaussianReal 0 1)`, and the
convergence is asserted for every real `α`. -/
theorem theorem_B {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ψ : ℝ → ℝ) (hψ_mono : Monotone ψ) (hψ_unbdd : ¬ BddAbove (Set.range ψ))
    (m : ℝ → Ω → ℕ) (hm_meas : ∀ t, Measurable (m t)) (hm_pos : ∀ t ω, 1 ≤ m t ω)
    (hm_ratio : TendstoInMeasure P (fun t ω => (m t ω : ℝ) / ψ t) atTop (fun _ => 1))
    (y : ℕ → Ω → ℝ) (hy_indep : iIndepFun (fun i => y (i + 1)) P)
    (hy_ident : ∀ i, IdentDistrib (y (i + 1)) (y 1) P P)
    (hy_L2 : MemLp (y 1) 2 P) (hy_mean : ∫ ω, y 1 ω ∂P = 0)
    (σ : ℝ) (hσ_pos : 0 < σ) (hy_var : variance (y 1) P = σ ^ 2) :
    ∀ α : ℝ, Tendsto
      (fun t : ℝ => P.real {ω | (∑ i ∈ Finset.Icc 1 (m t ω), y i ω) / (σ * Real.sqrt (ψ t)) ≤ α})
      atTop (𝓝 (cdf (gaussianReal 0 1) α)) := by sorry

end SmithRegenerative.CLT

