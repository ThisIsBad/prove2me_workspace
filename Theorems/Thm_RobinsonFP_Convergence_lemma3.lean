import Mathlib
import Definitions.Def_RobinsonFP_Convergence_VectorSystem

namespace RobinsonFP.Convergence

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Robinson (1951), p. 299, Lemma 3: if every row and every column is eligible in `(s, s + t)`,
then `max V(s+t) − min U(s+t) ≤ 4at`, for any `a` bounding every `|a_ij|`. -/
theorem lemma3 [Nonempty ι] [Nonempty κ] (A : Matrix ι κ ℝ) (a : ℝ) (ha : ∀ i j, |A i j| ≤ a)
    (U : ℕ → κ → ℝ) (V : ℕ → ι → ℝ) (hUV : IsVectorSystem A U V) (s t : ℕ)
    (hrow : ∀ i, RowEligible V i s (s + t)) (hcol : ∀ j, ColEligible U j s (s + t)) :
    vmax (V (s + t)) - vmin (U (s + t)) ≤ 4 * a * t := by sorry

end RobinsonFP.Convergence

