import Mathlib

/-!
# Theorem 2.2.1: the queueing proof of the pointwise ergodic theorem (§2.2.5, p.90)
-/

namespace PalmQueueing.Loynes

open MeasureTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Theorem 2.2.1** (§2.2.5, p.90). Whenever `(P⁰, θ)` is ergodic and both `σ` and `τ` are
non-negative, not identically null, and integrable,

`lim_{n→∞} ( Σ_{i=0}^{n} σ ∘ θ^{-i} ) / ( Σ_{i=0}^{n} τ ∘ θ^{-i} ) = E⁰[σ] / E⁰[τ]`,  `P⁰`-a.s.

The section's title is "Queueing Proof of the Ergodic Theorem", and the point is the direction of
the argument: the queueing construction of §2.2 — Loynes' monotone scheme, Hopf's lemma (2.2.18)
and the stability criterion — *yields* the pointwise ergodic theorem, rather than being derived
from it. The ratio form is the natural output of that route, since what the queue supplies is the
comparison `Σ σ ∘ θ^{-i} ≤ Σ τ ∘ θ^{-i} + M_n` with `M_n ↑ M_∞ < ∞`.

Mathlib's `Ergodic` is reused rather than a private notion; Mathlib has the *mean* ergodic theorem
but no pointwise one, so nothing here duplicates it. -/
theorem queueing_ergodic_theorem (P0 : Measure Ω) [IsProbabilityMeasure P0]
    (shift : Ω ≃ᵐ Ω) (herg : Ergodic shift P0)
    (sig tau : Ω → ℝ) (hsigmeas : Measurable sig) (htaumeas : Measurable tau)
    (hsig0 : ∀ ω, 0 ≤ sig ω) (htau0 : ∀ ω, 0 ≤ tau ω)
    (hsigNull : ¬ (∀ᵐ ω ∂P0, sig ω = 0)) (htauNull : ¬ (∀ᵐ ω ∂P0, tau ω = 0))
    (hsigInt : Integrable sig P0) (htauInt : Integrable tau P0) :
    ∀ᵐ ω ∂P0, Tendsto
      (fun n : ℕ =>
        (∑ i ∈ Finset.range (n + 1), sig ((shift.symm^[i]) ω)) /
        (∑ i ∈ Finset.range (n + 1), tau ((shift.symm^[i]) ω)))
      atTop (𝓝 ((∫ ω, sig ω ∂P0) / ∫ ω, tau ω ∂P0)) := by sorry

end PalmQueueing.Loynes

