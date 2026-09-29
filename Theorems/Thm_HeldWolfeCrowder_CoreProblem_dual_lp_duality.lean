import Mathlib
import Definitions.Def_HeldWolfeCrowder_CoreProblem_Setting

namespace HeldWolfeCrowder.CoreProblem

open scoped InnerProductSpace
open Filter Topology

/-- **Held, Wolfe & Crowder (1974), Eq. (6.1), p. 81.** Linear-programming duality between
`max w` (the problem `max {z : z − π·v_k ≤ c_k for all k}`) and its dual (6.1): if `w` is
bounded above, then `w` attains its maximum at some `π*`, (6.1) has an optimal solution `y`,
and the two optimal values agree, `Σ_k c_k y_k = w(π*) = max w`. -/
theorem dual_lp_duality {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (c : ι → ℝ) (v : ι → EuclideanSpace ℝ (Fin n)) (hw : BddAbove (Set.range (w c v))) :
    ∃ (πstar : EuclideanSpace ℝ (Fin n)) (y : ι → ℝ),
      (∀ π', w c v π' ≤ w c v πstar) ∧ IsDualOptimal c v y ∧ dualObj c y = w c v πstar := by sorry

end HeldWolfeCrowder.CoreProblem

