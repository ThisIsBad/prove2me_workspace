import Mathlib
import Definitions.Def_LinearOptimization_DualLP

open Matrix

namespace AdaptiveStepIPM.PredCorr

/-- The Euclidean norm used without a subscript in the report, p. 2. -/
noncomputable def l2Norm {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ j, (v j) ^ 2)

/-- The duality measure μ = xᵀs/n. -/
noncomputable def mu {n : ℕ} (x s : Fin n → ℝ) : ℝ :=
  (x ⬝ᵥ s) / (n : ℝ)

/-- The strictly feasible primal and dual pairs F⁰, with the dual multiplier existential. -/
def F0 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (x s : Fin n → ℝ) : Prop :=
  x ∈ LinearOptimization.generalFeasibleSet (LinearOptimization.stdFormLP A b c) ∧
  (∃ y : Fin m → ℝ, Aᵀ *ᵥ y + s = c) ∧
  (∀ j, 0 < x j) ∧ (∀ j, 0 < s j)

/-- The report's Euclidean central-path neighborhood N₂(β), pp. 1–2. -/
def N2 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (β : ℝ)
    (x s : Fin n → ℝ) : Prop :=
  F0 A b c x s ∧
  l2Norm (fun j => x j * s j - mu x s) ≤ β * mu x s

end AdaptiveStepIPM.PredCorr
