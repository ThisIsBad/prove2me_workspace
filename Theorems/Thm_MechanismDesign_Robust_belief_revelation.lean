import Mathlib
import Definitions.Def_MechanismDesign_Robust_Mechanisms

open scoped ENNReal

namespace MechanismDesign.Robust

/-- Proposition 10.6 (Börgers p.183; Bergemann–Morris 2001, Prop. 4.5), belief revelation on a
finite type space with quasi-linear utilities `v_i(a, θ) − t_i`. Suppose
(i) for every agent `i`, no belief in the set `{β̂_i(τ_i) : τ_i ∈ T_i}` (as a vector in
`ℝ^{T_{-i}}`) is a convex combination of the other beliefs in that set, and the direct mechanism
`(q, t)` satisfies
(ii) for every agent `i` and types `τ_i, τ'_i` with `β̂_i(τ_i) = β̂_i(τ'_i)`, type `τ_i` has no
incentive to pretend to be `τ'_i` (others reporting truthfully).
Then there is another direct mechanism `(q̃, t̃)` in which truth telling is a Bayesian equilibrium,
such that (iii) `q̃(τ) = q(τ)` for every type profile `τ`, and (iv) every type `τ_i` has the same
interim expected payment in both mechanisms. -/
theorem belief_revelation {ι : Type} [Fintype ι] [DecidableEq ι] {Θ T : ι → Type*} {A : Type*}
    [∀ i, Fintype (T i)] (ts : TypeSpace Θ T) (vu : ι → A → (∀ i, Θ i) → ℝ)
    (hconv : ∀ i (τi : T i), (fun τo => (ts.β i τi τo).toReal) ∉
      convexHull ℝ ((fun τi' : T i => fun τo => (ts.β i τi' τo).toReal) ''
        {τi' | ts.β i τi' ≠ ts.β i τi}))
    (q : (∀ i, T i) → A) (t : ι → (∀ i, T i) → ℝ)
    (hsame : ∀ i (τi τi' : T i), ts.β i τi = ts.β i τi' →
      interimEU ts (qlUtility vu) (qlDirect ts q t) (truthful T) i τi (PMF.pure τi') ≤
        interimEU ts (qlUtility vu) (qlDirect ts q t) (truthful T) i τi (PMF.pure τi)) :
    ∃ (q' : (∀ i, T i) → A) (t' : ι → (∀ i, T i) → ℝ),
      IsBayesEq ts (qlUtility vu) (qlDirect ts q' t') (truthful T) ∧
      (∀ τ, q' τ = q τ) ∧
      ∀ i (τi : T i), interimPayment ts t' i τi = interimPayment ts t i τi := by sorry

end MechanismDesign.Robust

