import Mathlib
import Definitions.Def_CrossSell_Pricing_Model

namespace CrossSell.Pricing

theorem H_fixed_point {ι κ : Type*} [Fintype κ] (S : Finset ι) (T : Option ι → Finset κ)
    (u c : ι → ℝ) (s : κ → ℝ) (v : Option ι → κ → ℝ) :
    (∀ z : ℝ, BddAbove (Set.range fun r : κ → ℝ => Hr S T u c s v r z)) ∧
    (∃! z : ℝ, z = Hmax S T u c s v z) ∧
    (S.Nonempty → StrictAnti (Hmax S T u c s v)) := by sorry

end CrossSell.Pricing

