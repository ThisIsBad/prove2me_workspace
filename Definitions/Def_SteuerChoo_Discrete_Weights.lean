import Mathlib
import Definitions.Def_SteuerChoo_Discrete_Nondominated
import Definitions.Def_SteuerChoo_Discrete_Tchebycheff

/-!
# Steuer–Choo (1983), §3: the weights `λᵖ` of (b), the values `α_pq` of (c)–(d), `ρ_p` of (3.6) and
`ρ` of (3.8)

R. E. Steuer and E.-U. Choo, Math. Programming 26 (1983), §3, pp. 330–332.

**Empty minima.** The minima in (3.6) and (3.8) range over sets that can be empty (e.g. when no
`z^q ∈ Z` has a larger coordinate sum than `z^p`). The paper does not assign a value in that case;
here the value is then `1` (any positive value would do; `0` would not).
-/

namespace SteuerChoo.Discrete

/-- The weights `λᵖ` of (b), §3, p. 330:
`λᵖᵢ = [1/(z*ᵢ − zᵖᵢ)] [Σⱼ 1/(z*ⱼ − zᵖⱼ)]⁻¹` if `zᵖᵢ ≠ z*ᵢ` for all `i`;
`λᵖᵢ = 1` if `zᵖᵢ = z*ᵢ`; `λᵖᵢ = 0` if `zᵖᵢ ≠ z*ᵢ` but `zᵖⱼ = z*ⱼ` for some `j`. -/
noncomputable def lamP {k : ℕ} (zstar zp : Fin k → ℝ) : Fin k → ℝ := by
  classical
  exact fun i =>
    if ∀ j, zp j ≠ zstar j then
      (1 / (zstar i - zp i)) * (∑ j, 1 / (zstar j - zp j))⁻¹
    else if zp i = zstar i then 1 else 0

/-- `α_pq` of (d), §3, p. 331: the minimal value of `min {α} s.t. α ≥ λᵖᵢ(z*ᵢ − z^qᵢ), 1 ≤ i ≤ k`,
i.e. `maxᵢ λᵖᵢ(z*ᵢ − z^qᵢ)`. With `zq = zp` this is `α_pp` of (c), p. 330. -/
noncomputable def alphaPQ {k : ℕ} [NeZero k] (zstar zp zq : Fin k → ℝ) : ℝ :=
  tcheb (lamP zstar zp) zstar zq

/-- `ρ_p` of (3.6), §3, p. 332:
`ρ_p = ½ min_{q ∈ I_Z − {p}} {(α_pq − α_pp) / eᵀ(z^q − zᵖ) | eᵀ(z^q − zᵖ) > 0}`,
and `1` when no `z^q ∈ Z` satisfies `eᵀ(z^q − zᵖ) > 0`. -/
noncomputable def rhoP {k : ℕ} [NeZero k] (Z : Finset (Fin k → ℝ)) (zstar zp : Fin k → ℝ) : ℝ := by
  classical
  exact
    let T := Z.filter (fun zq => 0 < ∑ i, (zq i - zp i))
    if h : T.Nonempty then
      (1 / 2) * T.inf' h
        (fun zq => (alphaPQ zstar zp zq - alphaPQ zstar zp zp) / ∑ i, (zq i - zp i))
    else 1

/-- `ρ` of (3.8), §3, p. 332:
`ρ = ½ min_{i ∈ I_N} [min_{j ∈ I_Z − {i}} {(α_ij − α_ii) / eᵀ(zʲ − zⁱ) | eᵀ(zʲ − zⁱ) > 0}]`,
the minimum taken over all pairs `(zⁱ, zʲ) ∈ N × Z` with `eᵀ(zʲ − zⁱ) > 0`, where `α_ij` is (d)
with the weights `λⁱ` of `zⁱ`; and `1` when there is no such pair. -/
noncomputable def rho38 {k : ℕ} [NeZero k] (Z : Finset (Fin k → ℝ)) (zstar : Fin k → ℝ) : ℝ := by
  classical
  exact
    let T := (nondominated Z ×ˢ Z).filter (fun pr => 0 < ∑ i, (pr.2 i - pr.1 i))
    if h : T.Nonempty then
      (1 / 2) * T.inf' h
        (fun pr => (alphaPQ zstar pr.1 pr.2 - alphaPQ zstar pr.1 pr.1) / ∑ i, (pr.2 i - pr.1 i))
    else 1

end SteuerChoo.Discrete
