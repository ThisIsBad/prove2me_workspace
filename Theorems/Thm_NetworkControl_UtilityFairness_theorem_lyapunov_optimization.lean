import Mathlib
import Definitions.Def_NetworkControl_UtilityFairness_drift

namespace NetworkControl.UtilityFairness

open MeasureTheory

/-- Theorem 5.4 (Lyapunov Optimization), p. 82. If there are positive constants `V, ε, B` such
that for all timeslots `t`, `∆(U(t)) - V·E{g(R(t))|U(t)} ≤ B - ε Σ_i U_i(t) - V·g*` (5.19), then
`limsup_t (1/t) Σ_τ Σ_i E{U_i(τ)} ≤ (B + V(g̅ - g*))/ε` (5.20) and `liminf_t g(r(t)) ≥ g* - B/V`
(5.21), where `r(t) := (1/t) Σ_τ E{R(τ)}` (5.18) and `g̅ := limsup_t (1/t) Σ_τ E{g(R(τ))}`. `g` is
any concave scalar-valued utility function of the `K`-dimensional rate vector; `g*` is an
arbitrary target value the hypothesis (5.19) is checked against, not necessarily the true
optimum. This names no algorithm and is the most self-contained capstone of the chapter.

**Formalization note.** `r(t)` and `g̅` are written out inline as the Cesàro averages (5.18) and
the definition preceding the theorem, rather than as separate named definitions, since each is
used exactly once. Explicit `Measurable`/`Integrable` guards on `U`, `R`, `g∘R` and the drift
terms prevent `condExp`/`∫` from silently defaulting to `0` (Faithfulness trap 2). -/
theorem theorem_lyapunov_optimization
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {N K : ℕ} (L : (Fin N → ℝ) → ℝ) (hLnn : ∀ u, 0 ≤ L u)
    (U : ℕ → Ω → Fin N → ℝ) (R : ℕ → Ω → Fin K → ℝ) (g : (Fin K → ℝ) → ℝ) (gstar : ℝ)
    (hgConcave : ConcaveOn ℝ Set.univ g)
    (V ε B : ℝ) (hV : 0 < V) (hε : 0 < ε) (hB : 0 < B)
    (hMeasU : ∀ t : ℕ, ∀ i : Fin N, Measurable (fun ω => U t ω i))
    (hIntegL0 : Integrable (fun ω => L (U 0 ω)) P)
    (hIntegLdrift : ∀ t : ℕ, Integrable (fun ω => L (U (t + 1) ω) - L (U t ω)) P)
    (hIntegG : ∀ t : ℕ, Integrable (fun ω => g (R t ω)) P)
    (hIntegU : ∀ t : ℕ, ∀ i : Fin N, Integrable (fun ω => U t ω i) P)
    (hIntegR : ∀ t : ℕ, ∀ k : Fin K, Integrable (fun ω => R t ω k) P)
    (hdrift : ∀ t : ℕ,
      ((fun ω => drift P L U t ω - V * (P[(fun ω => g (R t ω)) | MeasurableSpace.comap (U t) inferInstance]) ω))
        ≤ᵐ[P] (fun ω => B - ε * ∑ i : Fin N, U t ω i - V * gstar)) :
    (Filter.limsup
        (fun t : ℕ => (1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∑ i : Fin N, ∫ ω, U τ ω i ∂P)
        Filter.atTop
      ≤ (B + V * (Filter.limsup
            (fun t : ℕ => (1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∫ ω, g (R τ ω) ∂P)
            Filter.atTop
          - gstar)) / ε) ∧
    (Filter.liminf
        (fun t : ℕ => g (fun k : Fin K => (1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∫ ω, R τ ω k ∂P))
        Filter.atTop
      ≥ gstar - B / V) := by sorry

end NetworkControl.UtilityFairness
