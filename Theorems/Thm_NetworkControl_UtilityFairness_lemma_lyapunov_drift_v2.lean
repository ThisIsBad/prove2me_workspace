import Mathlib
import Definitions.Def_NetworkControl_UtilityFairness_drift


namespace NetworkControl.UtilityFairness

open MeasureTheory

/-- Lemma 5.3 (Lyapunov Drift), Georgiadis–Neely–Tassiulas p. 81. Let `L ≥ 0` be a Lyapunov
function of the backlog vector with `E L(U(0)) < ∞`. If there are scalar processes `x(t), y(t)`
such that for every slot `t` the drift satisfies `∆(U(t)) ≤ E{y(t) | U(t)} - E{x(t) | U(t)}`
(5.17), then
`limsup_t (1/t) Σ_{τ<t} E x(τ) ≤ limsup_t (1/t) Σ_{τ<t} E y(τ)`, and likewise for `liminf`.

Corrected version: both sides are read in the extended reals `EReal`, exactly as the monograph
intends (the inequality is trivially true when the `y`-averages diverge to `+∞`). The retired
version used `Filter.limsup` on `ℝ`, which returns the junk value `0` for a sequence unbounded
above, so a `y`-average tending to `+∞` was compared as if it were `0`. -/
theorem lemma_lyapunov_drift_v2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {N : ℕ} (L : (Fin N → ℝ) → ℝ) (hLnn : ∀ u, 0 ≤ L u)
    (U : ℕ → Ω → Fin N → ℝ) (x y : ℕ → Ω → ℝ)
    (hMeasU : ∀ t : ℕ, ∀ i : Fin N, Measurable (fun ω => U t ω i))
    (hIntegL : ∀ t : ℕ, Integrable (fun ω => L (U t ω)) P)
    (hIntegX : ∀ t : ℕ, Integrable (x t) P)
    (hIntegY : ∀ t : ℕ, Integrable (y t) P)
    (hdrift : ∀ t : ℕ,
      drift P L U t
        ≤ᵐ[P] ((P[y t | MeasurableSpace.comap (U t) inferInstance])
                - (P[x t | MeasurableSpace.comap (U t) inferInstance]))) :
    (Filter.limsup
        (fun t : ℕ => (((1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∫ ω, x τ ω ∂P : ℝ) : EReal))
        Filter.atTop
      ≤ Filter.limsup
        (fun t : ℕ => (((1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∫ ω, y τ ω ∂P : ℝ) : EReal))
        Filter.atTop) ∧
    (Filter.liminf
        (fun t : ℕ => (((1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∫ ω, x τ ω ∂P : ℝ) : EReal))
        Filter.atTop
      ≤ Filter.liminf
        (fun t : ℕ => (((1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∫ ω, y τ ω ∂P : ℝ) : EReal))
        Filter.atTop) := by sorry

end NetworkControl.UtilityFairness

