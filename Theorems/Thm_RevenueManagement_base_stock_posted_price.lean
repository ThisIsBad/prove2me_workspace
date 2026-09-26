import Definitions.Def_RevenueManagement_dynamicPricing

namespace RevenueManagement

variable {Ω : Type*} [MeasurableSpace Ω]

theorem base_stock_posted_price (M : ReplPricing Ω) (hM : M.IsModel) (t : ℕ) (ht : 1 ≤ t)
    (htT : t ≤ M.T) (y0 d0 : ℝ) (hd0 : d0 ∈ Set.Icc 0 M.dbar)
    (h0 : ∀ y d, d ∈ Set.Icc 0 M.dbar → M.objective t y d ≤ M.objective t y0 d0) :
    (∀ x, x ≤ y0 → M.IsOptimal t x y0 d0) ∧
    (∀ x, y0 ≤ x → ∃ d, d0 ≤ d ∧ M.IsOptimal t x x d) ∧
    (∀ x x' d, y0 ≤ x → x ≤ x' → M.IsOptimal t x x d →
      ∃ d', d ≤ d' ∧ M.IsOptimal t x' x' d') := by sorry

end RevenueManagement
