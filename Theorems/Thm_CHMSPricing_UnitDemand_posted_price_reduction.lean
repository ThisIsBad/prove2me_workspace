import Mathlib
import Definitions.Def_CHMSPricing_UnitDemand_Mechanism
import Definitions.Def_CHMSPricing_UnitDemand_MenuMech

namespace CHMSPricing.UnitDemand

/-- Theorem 4, p. 6: if the order-oblivious posted prices `p` `α`-approximate the optimal revenue
for the single-parameter instance `ℐ^copies` (`ℛ^{M'} ≤ α·ℛ^obl_p` for every truthful `M'`),
then for every arrival order `σ` the price-menu mechanism with prices `p` is truthful for the
BMUMD instance `ℐ` and `α`-approximates the revenue of every deterministic truthful
individually rational mechanism for `ℐ`. -/
theorem posted_price_reduction {J : Type*} [Fintype J] [DecidableEq J] {m : ℕ}
    (D : J → ValueDist) (𝒥 : SetSystem J) (owner : J → Fin m) (h𝒥 : IsUnitDemand 𝒥 owner)
    (p : J → ℝ) (α : ℝ) (hα : 0 ≤ α)
    (hopm : ∀ M' : Mechanism J, IsTruthful D 𝒥 M' → revenue D M' ≤ α * oblRevenue D 𝒥 p) :
    ∀ σ : Equiv.Perm (Fin m),
      IsTruthfulMulti D 𝒥 owner (menuMech 𝒥 owner σ p) ∧
      ∀ A : MultiMechanism J m, IsTruthfulMulti D 𝒥 owner A →
        revenueMulti D A ≤ α * revenueMulti D (menuMech 𝒥 owner σ p) := by sorry

end CHMSPricing.UnitDemand

