import Mathlib
import Definitions.Def_SteuerChoo_Discrete_Nondominated
import Definitions.Def_SteuerChoo_Discrete_Tchebycheff

namespace SteuerChoo.Discrete

/-- **Theorem 3.1** (Steuer–Choo 1983, p. 330): let `Z` be finite and let `M` be the set of
`z ∈ Z` minimizing the weighted Tchebycheff program. Then some `z̄ ∈ M` is nondominated.
Here `Z` is a nonempty finite set of criterion vectors, `λ ∈ Λ̄` and `z*` is arbitrary. -/
theorem theorem_3_1 {k : ℕ} [NeZero k] (Z : Finset (Fin k → ℝ)) (hZ : Z.Nonempty)
    (lam : Fin k → ℝ) (hlam : lam ∈ stdSimplex ℝ (Fin k)) (zstar : Fin k → ℝ) :
    ∃ zbar ∈ Z, (∀ z ∈ Z, tcheb lam zstar zbar ≤ tcheb lam zstar z) ∧ zbar ∈ nondominated Z := by sorry

end SteuerChoo.Discrete
