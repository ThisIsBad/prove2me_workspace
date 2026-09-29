import Mathlib
import Definitions.Def_WeylPolyhedra_Shared_Representable
import Definitions.Def_WeylPolyhedra_Shared_NonDegenerate
import Definitions.Def_WeylPolyhedra_Shared_IsExtremeSupport

namespace WeylPolyhedra.Pyramid

/-- Weyl (1935), §2 a), p. 292 (the modified first step of case a)): let `S ⊆ ℝⁿ` be finite and
non-degenerate, `β` an extreme support of `S`, and `p` a point satisfying every extreme support
inequality of `S`. Then there is a point `e ∈ S` with `β ⬝ᵥ e > 0` and a number `l ≥ 0` (Weyl's
`λ`) such that `q = p - l • e` still satisfies every extreme support inequality `α ⬝ᵥ q ≥ 0`,
and lies on the plane `α ⬝ᵥ q = 0` of at least one extreme support `α` with `α ⬝ᵥ e > 0` (an
extreme support of "the first class"). -/
theorem reduction_step {n : ℕ} (S : Finset (Fin n → ℝ)) (hS : Shared.NonDegenerate S)
    (β : Fin n → ℝ) (hβ : Shared.IsExtremeSupport S β) (p : Fin n → ℝ)
    (hp : ∀ α : Fin n → ℝ, Shared.IsExtremeSupport S α → 0 ≤ α ⬝ᵥ p) :
    ∃ e ∈ S, 0 < β ⬝ᵥ e ∧ ∃ l : ℝ, 0 ≤ l ∧
      (∀ α : Fin n → ℝ, Shared.IsExtremeSupport S α → 0 ≤ α ⬝ᵥ (p - l • e)) ∧
      ∃ α : Fin n → ℝ, Shared.IsExtremeSupport S α ∧ 0 < α ⬝ᵥ e ∧ α ⬝ᵥ (p - l • e) = 0 := by sorry

end WeylPolyhedra.Pyramid

