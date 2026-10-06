import Mathlib
import Definitions.Def_ConjugateConvex_Involution_conjDomain
import Definitions.Def_ConjugateConvex_Involution_conjFun
import Definitions.Def_ConjugateConvex_Involution_IsClosedConvexPair

namespace ConjugateConvex.Involution

/-- Fenchel (1949), §4, pp. 76–77, (7): for `x° ∉ G`, `l.u.b._{ξ∈Γ} (Σξx° − φ(ξ)) = ∞`, i.e. the
function `ξ ↦ Σξx° − φ(ξ)` is unbounded above on `Γ`, so `x° ∉ G*`. -/
theorem biconj_unbounded_off_domain {n : ℕ} (G : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (hGf : IsClosedConvexPair G f) :
    ∀ x₀ ∉ G,
      ¬ BddAbove ((fun ξ => ξ ⬝ᵥ x₀ - conjFun G f ξ) '' conjDomain G f) := by sorry

end ConjugateConvex.Involution

