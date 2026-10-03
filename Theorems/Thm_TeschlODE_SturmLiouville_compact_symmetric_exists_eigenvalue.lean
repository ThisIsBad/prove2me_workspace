import Mathlib
import Definitions.Def_TeschlODE_SturmLiouville_IsCompactOp

namespace TeschlODE.SturmLiouville

/-- Teschl, Theorem 5.5, p. 150: a compact symmetric operator `A` on a (nonzero) complex inner
product space `H₀` has an eigenvalue `α₀` with `|α₀| = ‖A‖ = sup_{‖f‖ = 1} ‖A f‖` (5.39).
The operator norm is stated as: `|α₀|` is the least upper bound of `{‖A f‖ : ‖f‖ = 1}`. -/
theorem compact_symmetric_exists_eigenvalue {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [Nontrivial E] (A : E →ₗ[ℂ] E) (hA : IsCompactOp A)
    (hsym : A.IsSymmetric) :
    ∃ α₀ : ℂ, (∃ u : E, u ≠ 0 ∧ A u = α₀ • u) ∧
      IsLUB {x : ℝ | ∃ f : E, ‖f‖ = 1 ∧ x = ‖A f‖} ‖α₀‖ := by sorry

end TeschlODE.SturmLiouville

