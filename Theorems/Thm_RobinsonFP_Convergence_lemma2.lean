import Mathlib
import Definitions.Def_RobinsonFP_Convergence_VectorSystem

namespace RobinsonFP.Convergence

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Robinson (1951), p. 298, Lemma 2: if every row and every column is eligible in `(s, s + t)`,
then `max U(s+t) − min U(s+t) ≤ 2at` and `max V(s+t) − min V(s+t) ≤ 2at`, for any `a` bounding
every `|a_ij|` (in particular `a = max_{i,j} |a_ij|`). -/
theorem lemma2 [Nonempty ι] [Nonempty κ] (A : Matrix ι κ ℝ) (a : ℝ) (ha : ∀ i j, |A i j| ≤ a)
    (U : ℕ → κ → ℝ) (V : ℕ → ι → ℝ) (hUV : IsVectorSystem A U V) (s t : ℕ)
    (hrow : ∀ i, RowEligible V i s (s + t)) (hcol : ∀ j, ColEligible U j s (s + t)) :
    vmax (U (s + t)) - vmin (U (s + t)) ≤ 2 * a * t ∧
      vmax (V (s + t)) - vmin (V (s + t)) ≤ 2 * a * t := by sorry

end RobinsonFP.Convergence

