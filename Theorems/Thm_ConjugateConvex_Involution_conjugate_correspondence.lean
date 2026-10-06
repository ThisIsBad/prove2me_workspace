import Mathlib
import Definitions.Def_ConjugateConvex_Involution_conjDomain
import Definitions.Def_ConjugateConvex_Involution_conjFun
import Definitions.Def_ConjugateConvex_Involution_IsClosedConvexPair

namespace ConjugateConvex.Involution

/-- Fenchel (1949), §3, p. 75, the Theorem, with (5); proved in §§3–4, pp. 75–77.
For `(G, f)` in the standing class, the conjugate `(Γ, φ)` is again in the class, satisfies (5)
with equality attained at every (relative) interior point of `G`, and conjugates back to `(G, f)`
(`G* = G`, `f* = f` on `G`). Uniqueness is stated in the form the proof gives: any pair `(Γ′, φ′)`
in the class whose conjugate is `(G, f)` is `(Γ, φ)`. -/
theorem conjugate_correspondence {n : ℕ} (G : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (hGf : IsClosedConvexPair G f) :
    IsClosedConvexPair (conjDomain G f) (conjFun G f) ∧
    (∀ x ∈ G, ∀ ξ ∈ conjDomain G f, x ⬝ᵥ ξ ≤ f x + conjFun G f ξ) ∧
    (∀ x ∈ intrinsicInterior ℝ G, ∃ ξ ∈ conjDomain G f, x ⬝ᵥ ξ = f x + conjFun G f ξ) ∧
    conjDomain (conjDomain G f) (conjFun G f) = G ∧
    (∀ x ∈ G, conjFun (conjDomain G f) (conjFun G f) x = f x) ∧
    (∀ (Γ' : Set (Fin n → ℝ)) (φ' : (Fin n → ℝ) → ℝ), IsClosedConvexPair Γ' φ' →
      conjDomain Γ' φ' = G → (∀ x ∈ G, conjFun Γ' φ' x = f x) →
      Γ' = conjDomain G f ∧ ∀ ξ ∈ Γ', φ' ξ = conjFun G f ξ) := by sorry

end ConjugateConvex.Involution

