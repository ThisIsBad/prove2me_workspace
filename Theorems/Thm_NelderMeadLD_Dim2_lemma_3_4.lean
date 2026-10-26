import Mathlib
import Definitions.Def_NelderMeadLD_Dim2_Algorithm
open Filter Topology

namespace NelderMeadLD.Dim2

theorem lemma_3_4 {n : ℕ} [NeZero n] (f : E n → ℝ) (ρ χ γ σ : ℝ) (hpar : NelderMeadLD.Conv1D.ParamsOK ρ χ γ σ)
    (Δ : ℕ → Fin (n + 1) → E n) (hrun : IsNMRun f ρ χ γ σ Δ) (hnd : Nondegenerate (Δ 0))
    (hbdd : BddBelow (Set.range f)) (hnoshrink : ∀ k, ¬ IsShrinkAt f ρ χ γ Δ k)
    (j : Fin n) (a b : ℝ)
    (ha : Tendsto (fun k => f (Δ k j.castSucc)) atTop (𝓝 a))
    (hb : Tendsto (fun k => f (Δ k j.succ)) atTop (𝓝 b)) (hab : a < b) :
    ∃ K : ℕ, ∀ k ≥ K, ∀ i : Fin (n + 1), i ≤ j.castSucc → Δ (k + 1) i = Δ k i := by sorry

end NelderMeadLD.Dim2

