import Mathlib

namespace PhiDivRobust.Barrier

/-- Definition 1 (Ben-Tal et al. 2013, p. 350): `φ : F → ℝ` is `κ`-self-concordant on the open
convex set `F` if `κ ≥ 0`, `φ` is `C³` on `F`, and for every `y ∈ F` and every direction `h`,
`|∇³φ(y)[h,h,h]| ≤ 2κ (hᵀ∇²φ(y)h)^{3/2}`. -/
def IsSelfConcordant {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (κ : ℝ) (F : Set E) (φ : E → ℝ) : Prop :=
  0 ≤ κ ∧ IsOpen F ∧ Convex ℝ F ∧ ContDiffOn ℝ 3 φ F ∧
    ∀ y ∈ F, ∀ h : E,
      |iteratedFDeriv ℝ 3 φ y (fun _ => h)| ≤
        2 * κ * (iteratedFDeriv ℝ 2 φ y (fun _ => h)) ^ (3 / 2 : ℝ)

end PhiDivRobust.Barrier
