import Mathlib
import Definitions.Def_WhittleGittins_Retirement_BanditProcess

namespace WhittleGittins.Retirement

open MeasureTheory ProbabilityTheory

/-- Relation (18) (p. 147): `Pᵢ(x, s, M) = ∏_{j≠i} ∂φⱼ(xⱼ, sⱼ, M)/∂M` is, as a function of `M`,
non-negative, non-decreasing, at most one, and equal to one for `M ≥ M₍ᵢ₎ = max_{j≠i} Mⱼ` (the
maximum over the other active projects); moreover every index of an active project is `≤ K`. -/
theorem relation18_P_distribution {N : ℕ} {X : Fin N → Type*} [∀ i, MeasurableSpace (X i)]
    (B : BanditProcess N X) (x : ∀ j, X j) (s : Fin N → ℕ) (i : Fin N) :
    (∀ M, 0 ≤ Pdist B x s i M) ∧ Monotone (Pdist B x s i) ∧ (∀ M, Pdist B x s i M ≤ 1) ∧
      (∀ M, (∀ j, j ≠ i → 0 < s j → index B j (x j) (s j) ≤ M) → Pdist B x s i M = 1) ∧
      (∀ j, 0 < s j → index B j (x j) (s j) ≤ B.K) := by sorry

end WhittleGittins.Retirement

