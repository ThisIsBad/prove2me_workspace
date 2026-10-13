import Mathlib
import Definitions.Def_Disjunctive_GeneralDisjunctions_Cglp_v2


namespace Disjunctive.GeneralDisjunctions

/-- Theorem 11.11 (Balas, *Disjunctive Programming*, §11.5, p. 164-165; Balas–Kis 2016,
Theorem 11): let `w̄ := (ᾱ, β̄, {ūᵗ, ūᵗ₀})` be a basic feasible solution of (11.6) with `ūᵗ₀ > 0`
for all `t`. If `w̄` does not satisfy the condition of Theorem 11.9, and there is no basic
feasible solution `w̃` of (11.6) with `(α̃, β̃) = μ(ᾱ, β̄)` for some `μ > 0` that satisfies it, then
no intersection cut from `S` is equivalent to `ᾱx ≥ β̄`. Furthermore, if `(ᾱ, β̄)` uniquely
minimizes `αx̄_N - β` over (11.6), then `ᾱx̄_N - β̄ < α̃x̄_N - β̃` for every L&P cut `α̃x ≥ β̃` (an
`(α, β)`-component of a feasible solution of (11.6)) equivalent to an intersection cut from `S`,
and no such cut dominates `ᾱx ≥ β̄` on `P = {x : Ãx ≥ b̃}`.

Corrected from the retired version: `w̄` and the rescaled `w̃` are *basic* feasible solutions;
"intersection cut from `S`" ranges over genuine LP bases (injective, nonsingular, `ā0 ∈ int S`)
instead of arbitrary maps `ι`; the competing cuts `α̃x ≥ β̃` are L&P cuts, i.e. feasible for
(11.6) (otherwise rescaling `(α̃, β̃)` makes `α̃x̄_N - β̃` arbitrarily negative); and `P` is the LP
relaxation `{x : Ãx ≥ b̃}` rather than an arbitrary set. -/
theorem completeness_via_domination_v2 {n : ℕ} {M T : Type*} [Fintype M] [Fintype T]
    [Nonempty T] [DecidableEq M] [DecidableEq (Fin n)]
    (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (d : T → Fin n → ℝ) (d0 : T → ℝ)
    (xbarN : Fin n → ℝ)
    (alphaBar : Fin n → ℝ) (betaBar : ℝ) (u : T → M → ℝ) (u0 : T → ℝ)
    (hbasic : IsBasicCGLP116Solution Atil btil d d0 alphaBar u u0 betaBar)
    (hu0pos : ∀ t, 0 < u0 t)
    (hnot119 : ¬ SatisfiesThm119Condition Atil u)
    (hnoscaled119 : ∀ μ : ℝ, 0 < μ → ∀ u' u0',
      IsBasicCGLP116Solution Atil btil d d0 (μ • alphaBar) u' u0' (μ * betaBar) →
      ¬ SatisfiesThm119Condition Atil u') :
    ¬ IsEquivalentToIntersectionCutFromS Atil btil d d0 alphaBar betaBar ∧
      (IsCGLP116UniqueMin Atil btil d d0 xbarN alphaBar betaBar →
        ∀ alphaT : Fin n → ℝ, ∀ betaT : ℝ,
          (∃ uT u0T, IsCGLP116Feasible Atil btil d d0 alphaT uT u0T betaT) →
          IsEquivalentToIntersectionCutFromS Atil btil d d0 alphaT betaT →
          dotProduct alphaBar xbarN - betaBar < dotProduct alphaT xbarN - betaT ∧
            ¬ Dominates (LPPoly Atil btil) alphaT betaT alphaBar betaBar) := by sorry

end Disjunctive.GeneralDisjunctions

