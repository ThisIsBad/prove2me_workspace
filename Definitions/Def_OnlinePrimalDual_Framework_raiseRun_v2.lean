import Mathlib
import Definitions.Def_OnlinePrimalDual_Framework_CoveringInstance

namespace OnlinePrimalDual.Framework

/-- The amount by which a continuous primal-dual algorithm of Buchbinder & Naor, *The Design of
Competitive Online Algorithms via a Primal-Dual Approach*, FnT TCS 2009, Section 4.2 (Algorithm 2,
p. 121, and Algorithm 3, p. 124) raises the dual variable `yⱼ` of the arriving covering
constraint `j`, given the dual vector `y` in hand (with `y j = 0`, `j` not yet having arrived)
and the algorithm's rule `xRule` computing the primal vector from the dual vector. The
algorithm "increases `yⱼ` continuously while `∑_{i ∈ S(j)} xᵢ < 1`", so `yⱼ` stops at the least
`s ≥ 0` at which the constraint becomes satisfied: the infimum of
`{s ≥ 0 | 1 ≤ ∑_{i ∈ S(j)} xRule (y[j ↦ s]) i}`. For the two rules of the book (`alg2X`,
`alg3X`) this set is an interval `[s*, ∞)` whenever `S(j) ≠ ∅` (both rules are monotone and
right-continuous in `yⱼ`, unbounded for `alg2X`, and reach `1` for `alg3X`), so the infimum is
exactly the stopping value. (`sInf ∅ = 0` on `ℝ`; the empty case arises only for `S(j) = ∅`,
an infeasible covering LP on which the book's loop never terminates, excluded by the theorems'
standing assumption `∀ j, (inst.S j).Nonempty`.) -/
noncomputable def raiseAmount {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    [DecidableEq J] (inst : CoveringInstance I J) (xRule : (J → ℝ) → I → ℝ) (y : J → ℝ)
    (j : J) : ℝ :=
  sInf {s : ℝ | 0 ≤ s ∧ 1 ≤ ∑ i ∈ inst.S j, xRule (Function.update y j s) i}

/-- The complete run of a continuous primal-dual algorithm (Algorithm 2 with `xRule = alg2X inst`,
Algorithm 3 with `xRule = alg3X inst`; Section 4.2, p. 121 and p. 124) on the instance `inst`,
the covering constraints arriving in the order `ord : List J` (one entry per constraint):
starting from `y = 0`, each arriving constraint `j` has its dual variable raised by
`raiseAmount inst xRule y j`, all other dual variables being left unchanged. The result is the
final dual/packing vector `y` the algorithm outputs, a function of the instance and the arrival
order only; the algorithm's final primal/covering vector is `xRule` of it. -/
noncomputable def raiseRun {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (inst : CoveringInstance I J) (xRule : (J → ℝ) → I → ℝ) (ord : List J) : J → ℝ :=
  ord.foldl (fun y j => Function.update y j (raiseAmount inst xRule y j)) (fun _ => 0)

end OnlinePrimalDual.Framework
