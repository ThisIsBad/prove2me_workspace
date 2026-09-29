import Mathlib
import Definitions.Def_JacksonJobshop_Equilibrium_System

namespace JacksonJobshop.Equilibrium

/-- Jackson (1963), p. 136, first claim of the proof sentence before Theorem (4.5): if `π > 0`,
then (4.6) `p(k) = π w(k) W(S(k))` defines a probability distribution over state vectors. -/
theorem product_form_is_distribution {N : ℕ} (sys : JobshopSystem N) (hπ : 0 < piConst sys) :
    (∀ k, 0 ≤ productForm sys k) ∧ HasSum (productForm sys) 1 := by sorry

end JacksonJobshop.Equilibrium
