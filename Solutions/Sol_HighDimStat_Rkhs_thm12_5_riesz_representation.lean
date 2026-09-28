import Mathlib

namespace HighDimStat.Rkhs

open scoped RealInnerProductSpace

end HighDimStat.Rkhs

open HighDimStat.Rkhs
open scoped RealInnerProductSpace

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (L : H →ₗ[ℝ] ℝ)
    (hL : ∃ M : ℝ, ∀ f : H, |L f| ≤ M * ‖f‖) :
    ∃! g : H, ∀ f : H, L f = ⟪f, g⟫ := by
  obtain ⟨M, hM⟩ := hL
  let Lc : H →L[ℝ] ℝ := L.mkContinuous M (fun f => by rw [Real.norm_eq_abs]; exact hM f)
  refine ⟨(InnerProductSpace.toDual ℝ H).symm Lc, ?_, ?_⟩
  · intro f
    rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
    rfl
  · intro g' hg'
    apply ext_inner_left ℝ
    intro f
    rw [← hg' f, real_inner_comm, InnerProductSpace.toDual_symm_apply]
    rfl
