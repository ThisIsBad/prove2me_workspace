import Mathlib
import Definitions.Def_RobinsonFP_Convergence_VectorSystem

namespace RobinsonFP.Convergence

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Robinson (1951), p. 299, Lemma 4: for every matrix `A` and `ε > 0` there is `t₀`, depending
only on `A` and `ε`, such that every vector system `(U, V)` for `A` satisfies
`max V(t) − min U(t) < εt` for all `t ≥ t₀`. -/
theorem lemma4 [Nonempty ι] [Nonempty κ] (A : Matrix ι κ ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ t₀ : ℕ, ∀ (U : ℕ → κ → ℝ) (V : ℕ → ι → ℝ), IsVectorSystem A U V →
      ∀ t : ℕ, t₀ ≤ t → vmax (V t) - vmin (U t) < ε * t := by sorry

end RobinsonFP.Convergence

