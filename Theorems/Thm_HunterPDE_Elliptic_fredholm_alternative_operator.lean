import Mathlib
import Definitions.Def_HunterPDE_Elliptic_Fredholm

namespace HunterPDE.Elliptic

/-- Theorem 4.50 of Hunter, *Notes on PDEs* (revised 6/18/2014), p. 124: let `T ∈ ℒ(ℋ)` be a
Fredholm operator on a Hilbert space with `ind T = 0`. Then one of two alternatives holds:
(1) `ker T* = 0`, `ker T = 0`, `ran T = ℋ`, `ran T* = ℋ`;
(2) `ker T* ≠ 0`; `ker T` and `ker T*` are finite-dimensional with the same dimension;
`ran T = (ker T*)^⊥` and `ran T* = (ker T)^⊥`.
`T*` is the Hilbert-space adjoint `ContinuousLinearMap.adjoint T`. -/
theorem fredholm_alternative_operator {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H] (T : H →L[𝕜] H) (hT : IsFredholm T)
    (hind : index T = 0) :
    (LinearMap.ker (ContinuousLinearMap.adjoint T : H →ₗ[𝕜] H) = ⊥ ∧
      LinearMap.ker (T : H →ₗ[𝕜] H) = ⊥ ∧
      LinearMap.range (T : H →ₗ[𝕜] H) = ⊤ ∧
      LinearMap.range (ContinuousLinearMap.adjoint T : H →ₗ[𝕜] H) = ⊤) ∨
    (LinearMap.ker (ContinuousLinearMap.adjoint T : H →ₗ[𝕜] H) ≠ ⊥ ∧
      FiniteDimensional 𝕜 (LinearMap.ker (T : H →ₗ[𝕜] H)) ∧
      FiniteDimensional 𝕜 (LinearMap.ker (ContinuousLinearMap.adjoint T : H →ₗ[𝕜] H)) ∧
      Module.finrank 𝕜 (LinearMap.ker (T : H →ₗ[𝕜] H)) =
        Module.finrank 𝕜 (LinearMap.ker (ContinuousLinearMap.adjoint T : H →ₗ[𝕜] H)) ∧
      LinearMap.range (T : H →ₗ[𝕜] H) =
        (LinearMap.ker (ContinuousLinearMap.adjoint T : H →ₗ[𝕜] H))ᗮ ∧
      LinearMap.range (ContinuousLinearMap.adjoint T : H →ₗ[𝕜] H) =
        (LinearMap.ker (T : H →ₗ[𝕜] H))ᗮ) := by sorry

end HunterPDE.Elliptic
