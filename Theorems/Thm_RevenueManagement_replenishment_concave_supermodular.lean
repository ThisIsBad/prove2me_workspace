import Definitions.Def_RevenueManagement_dynamicPricing

namespace RevenueManagement

variable {Ω : Type*} [MeasurableSpace Ω]

theorem replenishment_concave_supermodular (M : ReplPricing Ω) (hM : M.IsModel) (t : ℕ)
    (ht : 1 ≤ t) (htT : t ≤ M.T) :
    ConcaveOn ℝ (Set.univ ×ˢ Set.Icc 0 M.dbar) (fun yd : ℝ × ℝ => M.contValue t yd.1 yd.2) ∧
    ConcaveOn ℝ Set.univ (M.value t) ∧
    (∀ y y' d d', y ≤ y' → d ∈ Set.Icc 0 M.dbar → d' ∈ Set.Icc 0 M.dbar → d ≤ d' →
      M.contValue t y d' - M.contValue t y d ≤ M.contValue t y' d' - M.contValue t y' d) := by sorry

end RevenueManagement
