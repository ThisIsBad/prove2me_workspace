import Mathlib
import Definitions.Def_DermanSeqDecisions_LinProg_LinearFractional

namespace CuttingStock63.Fractional
open DermanSeqDecisions.LinProg
theorem ratio_monotone_on_line {n : ℕ} (c d x v : Fin n → ℝ) (I : Set ℝ)
    (hI : IsPreconnected I) (hden : ∀ τ ∈ I, ∑ i, d i * (x + τ • v) i ≠ 0) :
    (StrictMonoOn (fun τ : ℝ => fracObj c d (x + τ • v)) I ∨
      StrictAntiOn (fun τ : ℝ => fracObj c d (x + τ • v)) I ∨
      ∀ τ ∈ I, ∀ τ' ∈ I, fracObj c d (x + τ • v) = fracObj c d (x + τ' • v)) ∧
    ∀ τ ∈ I, ∀ τ' ∈ I,
      deriv (fun s : ℝ => fracObj c d (x + s • v)) τ * (∑ i, d i * (x + τ • v) i) ^ 2 =
        deriv (fun s : ℝ => fracObj c d (x + s • v)) τ' * (∑ i, d i * (x + τ' • v) i) ^ 2 := by sorry
end CuttingStock63.Fractional

