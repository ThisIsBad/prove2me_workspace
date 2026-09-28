import Mathlib
import Definitions.Def_BealeConvexMin_SumLargest_sumLargest
import Definitions.Def_BealeConvexMin_SumLargest_Forms

namespace BealeConvexMin.SumLargest

/-- Beale (1955), §4, p. 179 (the paragraph before Theorem 1): "`C` can easily be shown to be
convex". Here `C = A + ` (sum of the `τ` largest of `L_0, …, L_s`), with `τ` at most the number
`s + 1` of forms, is convex as a function of all the variables `(z, u)`. -/
theorem C_convex {r s : ℕ} (P : Forms r s) (τ : ℕ) (hτ : τ ≤ s + 1) :
    ConvexOn ℝ Set.univ (fun p : (Fin r → ℝ) × (Fin s → ℝ) => P.C τ p.1 p.2) := by sorry

end BealeConvexMin.SumLargest

