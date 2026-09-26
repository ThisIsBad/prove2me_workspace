import Definitions.Def_RevenueManagement_auctions

namespace RevenueManagement

theorem first_price_equilibrium (V : PrivateValues) (hV : V.IsRegular) (hN : 2 ≤ V.N) :
    (∀ v ∈ Set.Ioc 0 V.vbar, HasDerivWithinAt (firstPriceBid V)
        ((((V.N : ℝ) - 1) * V.F v ^ (V.N - 2) * V.f v / firstPriceWinProb V v) *
          (v - firstPriceBid V v)) (Set.Icc 0 V.vbar) v) ∧
    (∀ v ∈ Set.Icc 0 V.vbar, ∀ w ∈ Set.Icc 0 V.vbar,
      firstPriceWinProb V w * (v - firstPriceBid V w) ≤
        firstPriceWinProb V v * (v - firstPriceBid V v)) ∧
    (∀ v ∈ Set.Ioc 0 V.vbar, firstPriceBid V v < v) := by sorry

end RevenueManagement
