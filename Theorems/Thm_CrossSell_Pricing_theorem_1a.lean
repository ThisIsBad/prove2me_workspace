import Mathlib
import Definitions.Def_CrossSell_Pricing_Model

namespace CrossSell.Pricing

theorem theorem_1a {ι κ : Type*} (S : Finset ι) (T : Option ι → Finset κ)
    (u c : ι → ℝ) (s : κ → ℝ) (v : Option ι → κ → ℝ) (p : ι → ℝ) (r : κ → ℝ)
    (hopt : ∀ (p' : ι → ℝ) (r' : κ → ℝ), profit S T u c s v p' r' ≤ profit S T u c s v p r) :
    ∀ i ∈ S, ∀ j ∈ S, aggMarkup T c s v p r i = aggMarkup T c s v p r j := by sorry

end CrossSell.Pricing

