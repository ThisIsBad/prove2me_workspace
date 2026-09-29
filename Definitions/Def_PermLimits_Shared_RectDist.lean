import Mathlib

/-!
# The rectangular distance between limit permutations

C. Hoppen, Y. Kohayakawa, C. G. Moreira, B. Ráth, R. M. Sampaio, *Limits of permutation
sequences*, arXiv:1103.5844v2, p. 12, Eq. (32) (first line), and Eq. (36), p. 13.
-/

namespace PermLimits.Shared

open MeasureTheory unitInterval

/-- **Rectangular distance** `d□(Z₁, Z₂)` (Hoppen et al., arXiv:1103.5844v2, Eq. (32), first
line, p. 12):
`d□(Z₁, Z₂) = sup_{x₁ < x₂, y₁ < y₂ ∈ [0,1]} | ∫_{x₁}^{x₂} (Z₁(x,y₂) − Z₁(x,y₁)) dx
− ∫_{x₁}^{x₂} (Z₂(x,y₂) − Z₂(x,y₁)) dx |`.

**Formalization Note.** The supremum is the real `sSup` of the set of values. For
`Z₁, Z₂ ∈ 𝒵` every value lies in `[0, 2]` (in fact in `[0, 1]`), so the set is nonempty and
bounded and `sSup` is the true supremum; statements apply `rectDist` only to limit permutations.
`∫_{x₁}^{x₂}` is the Lebesgue integral over `[x₁, x₂] ⊆ [0, 1]`. The rectangular distance
between a permutation `σ` and `Z` is `d□(σ, Z) := d□(Z_σ, Z)` (Eq. (36), p. 13), written
`rectDist (stepLimit σ) Z`. -/
noncomputable def rectDist (Z₁ Z₂ : I → I → ℝ) : ℝ :=
  sSup {r : ℝ | ∃ x₁ x₂ y₁ y₂ : I, x₁ < x₂ ∧ y₁ < y₂ ∧
    r = |(∫ x in Set.Icc x₁ x₂, (Z₁ x y₂ - Z₁ x y₁)) -
          (∫ x in Set.Icc x₁ x₂, (Z₂ x y₂ - Z₂ x y₁))|}

end PermLimits.Shared
