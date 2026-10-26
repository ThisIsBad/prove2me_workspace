import Mathlib
import Definitions.Def_NelderMeadLD_Dim2_Algorithm
open Filter Topology

namespace NelderMeadLD.Dim2

theorem corollary_3_1 {n : ℕ} [NeZero n] (f : E n → ℝ) (ρ χ γ σ : ℝ) (hpar : NelderMeadLD.Conv1D.ParamsOK ρ χ γ σ)
    (Δ : ℕ → Fin (n + 1) → E n) (hrun : IsNMRun f ρ χ γ σ Δ) (hnd : Nondegenerate (Δ 0))
    (hbdd : BddBelow (Set.range f)) (hnoshrink : ∀ k, ¬ IsShrinkAt f ρ χ γ Δ k)
    (hinf : ∀ N : ℕ, ∃ k ≥ N, Δ (k + 1) 0 ≠ Δ k 0) :
    ∃ L : ℝ, ∀ i, Tendsto (fun k => f (Δ k i)) atTop (𝓝 L) := by sorry

end NelderMeadLD.Dim2

