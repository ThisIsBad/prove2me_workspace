import Mathlib
import Definitions.Def_Disjunctive_LiftProject_Basic

namespace Disjunctive.LiftProject

/-- Theorem 6.4 (Balas §6.5, p. 86, eq. (6.5)-(6.6)): strengthening a lift-and-project cut
`αx ≥ β` from `(CGLP)_j` (with `α_i = max{α¹_i,α²_i}`) using integrality on the variables `N'`
yields a cut `γx ≥ β` valid for the full mixed 0-1 program, not merely for the single disjunction
on `j`. The premise is that `αx ≥ β` *is* a lift-and-project cut from `(CGLP)_j`: `u, v ≥ 0`,
`β = u b̃ = v b̃ + v₀` and `α_i = max{α¹_i, α²_i}`, the inequality form of (6.3) on p. 85. Bare
validity of `αx ≥ β` with unconstrained multipliers does not give a valid lifted cut: with
`n = 1`, `N' = {j}`, `K = {x_j = 1}`, `u = v = 0`, `u₀ = v₀ = 1`, `β = 1/2` the lifted cut reads
`0 ≥ 1/2` at the feasible point `x_j = 1`. -/
theorem mip_cut_lifting {n m : ℕ} (Atil : Matrix (Fin m) (Fin n) ℝ)
    (btil : Fin m → ℝ) (j : Fin n) (Nprime : Finset (Fin n))
    (u v : Fin m → ℝ) (u0 v0 : ℝ) (hu0 : 0 < u0) (hv0 : 0 < v0) (α : Fin n → ℝ) (β : ℝ)
    (hAlpha : ∀ i, α i = max (Alpha1_64 Atil u u0 j i) (Alpha2_64 Atil v v0 j i))
    (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hbeta1 : β = ∑ ρ, u ρ * btil ρ) (hbeta2 : β = (∑ ρ, v ρ * btil ρ) + v0)
    (γ mbar : Fin n → ℝ)
    (hmbar : ∀ k ∈ Nprime, mbar k = (Alpha2_64 Atil v v0 j k - Alpha1_64 Atil u u0 j k) / (u0 + v0))
    (hgamma1 : ∀ k ∈ Nprime, γ k = min (Alpha1_64 Atil u u0 j k + u0 * (⌈mbar k⌉ : ℝ))
      (Alpha2_64 Atil v v0 j k - v0 * (⌊mbar k⌋ : ℝ)))
    (hgamma2 : ∀ k ∉ Nprime, γ k = max (Alpha1_64 Atil u u0 j k) (Alpha2_64 Atil v v0 j k)) :
    ∀ x ∈ MIPDisjunctiveSet Atil btil Nprime, β ≤ dotProduct γ x := by sorry

end Disjunctive.LiftProject

