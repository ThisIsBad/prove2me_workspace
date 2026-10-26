import Mathlib
import Definitions.Def_NelderMeadLD_Dim2_Algorithm
open Filter Topology

namespace NelderMeadLD.Dim2

theorem lemma_3_3 {n : ℕ} [NeZero n] (f : E n → ℝ) (ρ χ γ σ : ℝ) (hpar : NelderMeadLD.Conv1D.ParamsOK ρ χ γ σ)
    (Δ : ℕ → Fin (n + 1) → E n) (hrun : IsNMRun f ρ χ γ σ Δ) (hnd : Nondegenerate (Δ 0))
    (hbdd : BddBelow (Set.range f)) :
    (∃ L : ℝ, Tendsto (fun k => f (Δ k 0)) atTop (𝓝 L)) ∧
    (∀ k, ¬ IsShrinkAt f ρ χ γ Δ k →
      (∀ i, f (Δ (k + 1) i) ≤ f (Δ k i)) ∧ ∃ i, f (Δ (k + 1) i) < f (Δ k i)) ∧
    (∀ K₀ : ℕ, (∀ k ≥ K₀, ¬ IsShrinkAt f ρ χ γ Δ k) →
      ∃ fstar : Fin (n + 1) → ℝ,
        (∀ i, Tendsto (fun k => f (Δ k i)) atTop (𝓝 (fstar i))) ∧
        (∀ i, ∀ k ≥ K₀, fstar i ≤ f (Δ k i)) ∧
        Monotone fstar) ∧
    (∀ K₀ : ℕ, (∀ k ≥ K₀, IsShrinkAt f ρ χ γ Δ k) →
      ∃ p : E n, ∀ i, Tendsto (fun k => Δ k i) atTop (𝓝 p)) := by sorry

end NelderMeadLD.Dim2

