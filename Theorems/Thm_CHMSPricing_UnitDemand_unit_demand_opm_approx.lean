import Mathlib
import Definitions.Def_CHMSPricing_UnitDemand_MenuMech

namespace CHMSPricing.UnitDemand

/-- Theorem 14, p. 9: `m` unit-demand buyers, items `K` with `cap k` copies of item `k`, and
independent regular values `v_{(i,k)} ∼ F_{(i,k)}` of each buyer for each item. There are prices
`p` such that, for every arrival order `σ`, the order-oblivious price-menu mechanism with prices
`p` is truthful and `6.75`-approximates the revenue of every deterministic truthful individually
rational mechanism. -/
theorem unit_demand_opm_approx {m : ℕ} {K : Type*} [Fintype K] [DecidableEq K]
    (cap : K → ℕ) (D : Fin m × K → ValueDist) (hreg : ∀ j, (D j).Regular) :
    ∃ p : Fin m × K → ℝ, ∀ σ : Equiv.Perm (Fin m),
      IsTruthfulMulti D (unitDemandSystem cap) Prod.fst
        (menuMech (unitDemandSystem cap) Prod.fst σ p) ∧
      ∀ A : MultiMechanism (Fin m × K) m,
        IsTruthfulMulti D (unitDemandSystem cap) Prod.fst A →
          revenueMulti D A ≤
            (27 / 4 : ℝ) * revenueMulti D (menuMech (unitDemandSystem cap) Prod.fst σ p) := by sorry

end CHMSPricing.UnitDemand

