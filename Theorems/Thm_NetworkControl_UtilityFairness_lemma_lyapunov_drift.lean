import Mathlib
import Definitions.Def_NetworkControl_UtilityFairness_drift

namespace NetworkControl.UtilityFairness

open MeasureTheory

/-- Lemma 5.3 (Lyapunov Drift), p. 81. Let `E{L(U(0))} < ∞`. If there exist scalar random
processes `x(t)` and `y(t)` such that for every timeslot `t`, the Lyapunov drift satisfies
`∆(U(t)) ≤ E{y(t)|U(t)} - E{x(t)|U(t)}` (5.17), then
`limsup_t (1/t) Σ_τ E{x(τ)} ≤ limsup_t (1/t) Σ_τ E{y(τ)}` and the same inequality holds for
`liminf`. This is the most abstract drift lemma in the book — even more general than Lemma 4.1,
since `x(t), y(t)` need not be linear in `U(t)`; Theorem 5.4 is derived from it by the
substitution `x(t) = ε Σ U_i(t) + V g*`, `y(t) = B + V g(R(t))`. -/
theorem lemma_lyapunov_drift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {N : ℕ} (L : (Fin N → ℝ) → ℝ) (hLnn : ∀ u, 0 ≤ L u)
    (U : ℕ → Ω → Fin N → ℝ) (x y : ℕ → Ω → ℝ)
    (hMeasU : ∀ t : ℕ, ∀ i : Fin N, Measurable (fun ω => U t ω i))
    (hIntegL0 : Integrable (fun ω => L (U 0 ω)) P)
    (hIntegLdrift : ∀ t : ℕ, Integrable (fun ω => L (U (t + 1) ω) - L (U t ω)) P)
    (hIntegX : ∀ t : ℕ, Integrable (x t) P)
    (hIntegY : ∀ t : ℕ, Integrable (y t) P)
    (hdrift : ∀ t : ℕ,
      drift P L U t
        ≤ᵐ[P] ((P[y t | MeasurableSpace.comap (U t) inferInstance])
                - (P[x t | MeasurableSpace.comap (U t) inferInstance]))) :
    (Filter.limsup (fun t : ℕ => (1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∫ ω, x τ ω ∂P)
        Filter.atTop
      ≤ Filter.limsup (fun t : ℕ => (1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∫ ω, y τ ω ∂P)
        Filter.atTop) ∧
    (Filter.liminf (fun t : ℕ => (1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∫ ω, x τ ω ∂P)
        Filter.atTop
      ≤ Filter.liminf (fun t : ℕ => (1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∫ ω, y τ ω ∂P)
        Filter.atTop) := by sorry

end NetworkControl.UtilityFairness
