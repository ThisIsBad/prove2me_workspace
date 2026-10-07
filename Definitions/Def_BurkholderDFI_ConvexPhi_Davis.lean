import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

namespace BurkholderDFI.ConvexPhi

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- §14, p. 33: yₖ = dₖ 1{|dₖ| ≤ 2d*ₖ₋₁}. -/
noncomputable def davisY (f : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  if |BurkholderDFI.SquareFnLp.dseq f k ω| ≤ 2 * (BurkholderDFI.SquareFnLp.maxFnN (BurkholderDFI.SquareFnLp.dseq f) (k - 1) ω).toReal then BurkholderDFI.SquareFnLp.dseq f k ω else 0

/-- §14, p. 33: zₖ = dₖ 1{|dₖ| > 2d*ₖ₋₁}. -/
noncomputable def davisZ (f : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  if 2 * (BurkholderDFI.SquareFnLp.maxFnN (BurkholderDFI.SquareFnLp.dseq f) (k - 1) ω).toReal < |BurkholderDFI.SquareFnLp.dseq f k ω| then BurkholderDFI.SquareFnLp.dseq f k ω else 0

/-- §14: aₖ = yₖ − E(yₖ|𝒜ₖ₋₁). -/
noncomputable def davisA (ℱ : Filtration ℕ mΩ) (P : Measure Ω) (f : ℕ → Ω → ℝ) (k : ℕ) : Ω → ℝ :=
  fun ω => davisY f k ω - (P[davisY f k | ℱ (k - 1)]) ω

/-- §14: bₖ = zₖ + E(yₖ|𝒜ₖ₋₁). -/
noncomputable def davisB (ℱ : Filtration ℕ mΩ) (P : Measure Ω) (f : ℕ → Ω → ℝ) (k : ℕ) : Ω → ℝ :=
  fun ω => davisZ f k ω + (P[davisY f k | ℱ (k - 1)]) ω

/-- (14.1): gₙ = ∑ₖ₌₁ⁿ aₖ. -/
noncomputable def davisG (ℱ : Filtration ℕ mΩ) (P : Measure Ω) (f : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => ∑ k ∈ Finset.Icc 1 n, davisA ℱ P f k ω

/-- (14.1): hₙ = ∑ₖ₌₁ⁿ bₖ. -/
noncomputable def davisH (ℱ : Filtration ℕ mΩ) (P : Measure Ω) (f : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => ∑ k ∈ Finset.Icc 1 n, davisB ℱ P f k ω

end BurkholderDFI.ConvexPhi
