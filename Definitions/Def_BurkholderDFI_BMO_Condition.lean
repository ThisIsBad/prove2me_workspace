import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

namespace BurkholderDFI.BMO

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- (19.1), p. 37: the conditional expectation given `𝒜_n` of the nonnegative sum
`∑_{k=n}^∞ d_k²` is at most one for each `n ≥ 1`. -/
def BMOCondition {Ω : Type*} [mΩ : MeasurableSpace Ω] (ℱ : Filtration ℕ mΩ)
    (P : Measure Ω) (f : ℕ → Ω → ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    condLExp (ℱ n) P (fun ω => ∑' j : ℕ, ENNReal.ofReal (BurkholderDFI.SquareFnLp.dseq f (n + j) ω ^ 2)) ≤ᵐ[P] 1

end BurkholderDFI.BMO
