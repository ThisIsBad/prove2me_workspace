import Mathlib
import Definitions.Def_CrossSell_Pricing_Model

namespace CrossSell.Pricing

theorem theorem_1 {ι κ : Type*} [Fintype κ] (S : Finset ι) (T : Option ι → Finset κ)
    (u c : ι → ℝ) (s : κ → ℝ) (v : Option ι → κ → ℝ) :
    (∀ (p : ι → ℝ) (r : κ → ℝ),
        (∀ (p' : ι → ℝ) (r' : κ → ℝ), profit S T u c s v p' r' ≤ profit S T u c s v p r) →
        ∀ i ∈ S, ∀ j ∈ S, aggMarkup T c s v p r i = aggMarkup T c s v p r j) ∧
    (∀ z : ℝ, BddAbove (Set.range fun r : κ → ℝ => Hr S T u c s v r z)) ∧
    (∃ zstar : ℝ, zstar = Hmax S T u c s v zstar ∧
        (∀ z : ℝ, z = Hmax S T u c s v z → z = zstar) ∧
        IsLUB (Set.range fun pr : (ι → ℝ) × (κ → ℝ) => profit S T u c s v pr.1 pr.2) zstar) ∧
    (S.Nonempty → StrictAnti (Hmax S T u c s v)) := by sorry

end CrossSell.Pricing

