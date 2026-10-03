import Mathlib

namespace HunterPDE.Elliptic

/-- Fredholm operator (Hunter, Definition 4.38): a bounded linear operator `T` on a Hilbert space
`H` is Fredholm if (a) `ker T` is finite-dimensional and (b) `ran T` is closed and has finite
codimension, where `codim ran T = dim (ran T)^⊥`. -/
def IsFredholm {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (T : H →L[𝕜] H) : Prop :=
  FiniteDimensional 𝕜 (LinearMap.ker (T : H →ₗ[𝕜] H)) ∧
    IsClosed (LinearMap.range (T : H →ₗ[𝕜] H) : Set H) ∧
    FiniteDimensional 𝕜 (LinearMap.range (T : H →ₗ[𝕜] H))ᗮ

/-- The index of a Fredholm operator (Definition 4.39):
`ind T = dim ker T − codim ran T = dim ker T − dim (ran T)^⊥`, an integer. (Meaningful when
`IsFredholm T`; both dimensions are then finite.) -/
noncomputable def index {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (T : H →L[𝕜] H) : ℤ :=
  (Module.finrank 𝕜 (LinearMap.ker (T : H →ₗ[𝕜] H)) : ℤ) -
    (Module.finrank 𝕜 (LinearMap.range (T : H →ₗ[𝕜] H))ᗮ : ℤ)

end HunterPDE.Elliptic
