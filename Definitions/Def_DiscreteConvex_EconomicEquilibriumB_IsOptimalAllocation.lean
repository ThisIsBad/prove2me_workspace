import Mathlib

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
variable {K : Type*} [Fintype K] [DecidableEq K]

/-- `(x,y)` is an optimal allocation of the MSFP2 associated with the economy: every bundle is in
its agent's effective domain, and no reallocation with the same aggregate excess achieves a larger
total surplus `∑ U_h(x_h) - ∑ C_l(y_l)`. Murota, *Discrete Convex Analysis*, SIAM 2003, §11.5
states Theorems 11.21 and 11.22 for such an allocation. -/
def IsOptimalAllocation {H L : Type*} [Fintype H] [Fintype L] (U : H → (K → ℤ) → WithBot ℝ)
    (C : L → (K → ℤ) → WithTop ℝ) (x : H → (K → ℤ)) (y : L → (K → ℤ)) : Prop :=
  (∀ h, U h (x h) ≠ ⊥) ∧ (∀ l, C l (y l) ≠ ⊤) ∧
  ∀ x' : H → (K → ℤ), ∀ y' : L → (K → ℤ),
    (∀ h, U h (x' h) ≠ ⊥) → (∀ l, C l (y' l) ≠ ⊤) →
    (∑ h, x' h) - (∑ l, y' l) = (∑ h, x h) - (∑ l, y l) →
    (∑ h, (U h (x' h)).unbotD 0) - (∑ l, (C l (y' l)).untopD 0) ≤
      (∑ h, (U h (x h)).unbotD 0) - (∑ l, (C l (y l)).untopD 0)

end DiscreteConvex.EconomicEquilibriumB
