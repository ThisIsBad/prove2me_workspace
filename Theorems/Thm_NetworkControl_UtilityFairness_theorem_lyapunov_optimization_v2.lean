import Mathlib
import Definitions.Def_NetworkControl_UtilityFairness_drift


namespace NetworkControl.UtilityFairness

open MeasureTheory

/-- Theorem 5.4 (Lyapunov Optimization), Georgiadis–Neely–Tassiulas p. 82. Let `L ≥ 0` with
`E L(U(0)) < ∞`, let `g` be a concave utility of the `K`-dimensional rate vector, and let
`V, ε, B > 0` be such that for every slot `t`
`∆(U(t)) - V·E{g(R(t)) | U(t)} ≤ B - ε Σ_i U_i(t) - V·g*` (5.19). Then, with
`r(t) := (1/t) Σ_{τ<t} E R(τ)` (5.18) and `ḡ := limsup_t (1/t) Σ_{τ<t} E g(R(τ))`,
`limsup_t (1/t) Σ_{τ<t} Σ_i E U_i(τ) ≤ (B + V(ḡ - g*))/ε` (5.20) and
`liminf_t g(r(t)) ≥ g* - B/V` (5.21).

Corrected version: `ḡ` and the two `limsup`/`liminf` are read in the extended reals `EReal`
(the monograph's `+∞` is not representable in `ℝ`, where `Filter.limsup` of an unbounded sequence
is the junk value `0`); (5.20) is written in the equivalent multiplied-out form
`ε · limsup ≤ B + V(ḡ - g*)` to avoid division in `EReal`. Backlogs are nonnegative, as
throughout the monograph. -/
theorem theorem_lyapunov_optimization_v2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {N K : ℕ} (L : (Fin N → ℝ) → ℝ) (hLnn : ∀ u, 0 ≤ L u)
    (U : ℕ → Ω → Fin N → ℝ) (R : ℕ → Ω → Fin K → ℝ) (g : (Fin K → ℝ) → ℝ) (gstar : ℝ)
    (hgConcave : ConcaveOn ℝ Set.univ g)
    (V ε B : ℝ) (hV : 0 < V) (hε : 0 < ε) (hB : 0 < B)
    (hUnn : ∀ t ω i, 0 ≤ U t ω i)
    (hMeasU : ∀ t : ℕ, ∀ i : Fin N, Measurable (fun ω => U t ω i))
    (hIntegL : ∀ t : ℕ, Integrable (fun ω => L (U t ω)) P)
    (hIntegG : ∀ t : ℕ, Integrable (fun ω => g (R t ω)) P)
    (hIntegU : ∀ t : ℕ, ∀ i : Fin N, Integrable (fun ω => U t ω i) P)
    (hIntegR : ∀ t : ℕ, ∀ k : Fin K, Integrable (fun ω => R t ω k) P)
    (hdrift : ∀ t : ℕ,
      ((fun ω => drift P L U t ω
          - V * (P[(fun ω => g (R t ω)) | MeasurableSpace.comap (U t) inferInstance]) ω))
        ≤ᵐ[P] (fun ω => B - ε * ∑ i : Fin N, U t ω i - V * gstar)) :
    ((ε : EReal) *
        Filter.limsup
          (fun t : ℕ =>
            (((1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∑ i : Fin N, ∫ ω, U τ ω i ∂P : ℝ) : EReal))
          Filter.atTop
      ≤ (B : EReal) + (V : EReal) *
          (Filter.limsup
            (fun t : ℕ => (((1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∫ ω, g (R τ ω) ∂P : ℝ) : EReal))
            Filter.atTop - (gstar : EReal))) ∧
    (((gstar - B / V : ℝ) : EReal) ≤
      Filter.liminf
        (fun t : ℕ =>
          ((g (fun k : Fin K => (1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∫ ω, R τ ω k ∂P) : ℝ) : EReal))
        Filter.atTop) := by sorry

end NetworkControl.UtilityFairness

