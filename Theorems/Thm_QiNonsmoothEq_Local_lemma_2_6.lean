import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
import Definitions.Def_NonsmoothNewton_Local_dirDeriv
import Definitions.Def_NonsmoothNewton_Local_SemismoothAt
import Definitions.Def_QiNonsmoothEq_Local_Setting
open Filter Topology

namespace QiNonsmoothEq.Local

/-- Qi (1993), Lemma 2.6, p. 233. If `F` is strongly BD-regular at `x`, there are a
neighbourhood `N` of `x` and a constant `c` such that for every `y ∈ N` and `V ∈ ∂_B F(y)`,
`V` is nonsingular with `‖V⁻¹‖ ≤ c` (2.13); if `F` is also semismooth at `y ∈ N`, then
`‖h‖ ≤ c ‖F'(y; h)‖` for every `h` (2.14). -/
theorem lemma_2_6 {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hF : LocallyLipschitz F) (x : EuclideanSpace ℝ (Fin n))
    (hreg : StronglyBDRegularAt F x) :
    ∃ N ∈ 𝓝 x, ∃ c : ℝ,
      (∀ y ∈ N, ∀ V ∈ NonsmoothNewton.Shared.bJac F y,
        ∃ W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n), IsInverse V W ∧ ‖W‖ ≤ c) ∧
      (∀ y ∈ N, NonsmoothNewton.Local.SemismoothAt F y →
        ∀ h : EuclideanSpace ℝ (Fin n), ‖h‖ ≤ c * ‖NonsmoothNewton.Local.dirDeriv F y h‖) := by sorry

end QiNonsmoothEq.Local

