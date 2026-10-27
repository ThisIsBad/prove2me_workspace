import Mathlib
import Definitions.Def_CrossSell_Pricing_Model

namespace CrossSell.Pricing

theorem optimal_price {ι κ : Type*} [Fintype κ] (S : Finset ι) (T : Option ι → Finset κ)
    (u c : ι → ℝ) (s : κ → ℝ) (v : Option ι → κ → ℝ) (zstar : ℝ) (rstar : κ → ℝ)
    (hz : zstar = Hmax S T u c s v zstar)
    (hr : ∀ r : κ → ℝ, Hr S T u c s v r zstar ≤ Hr S T u c s v rstar zstar) :
    profit S T u c s v (fun i => zstar + c i - secProfit T s v rstar (some i) + 1) rstar = zstar ∧
    ∀ (p : ι → ℝ) (r : κ → ℝ), profit S T u c s v p r ≤ zstar := by sorry

end CrossSell.Pricing

