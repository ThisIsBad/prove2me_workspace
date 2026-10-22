import Mathlib
import Definitions.Def_OnlinePrimalDual_Framework_CoveringInstance
import Definitions.Def_OnlinePrimalDual_Framework_dualSum
import Definitions.Def_OnlinePrimalDual_Framework_alg2X
import Definitions.Def_OnlinePrimalDual_Framework_raiseRun_v2


namespace OnlinePrimalDual.Framework

/-- **Theorem 4.2** (Buchbinder & Naor, FnT TCS 2009, p. 121-122), Algorithm 2, the continuous
algorithm. `ord` is the online arrival order of the covering constraints (a permutation of `J`);
`y = raiseRun inst (alg2X inst) ord` is Algorithm 2's own final dual vector (p. 121: each arriving
`yⱼ` is increased continuously *exactly while* `∑_{i ∈ S(j)} xᵢ < 1`, with `x` given by the
closed-form rule `alg2X`), and `x = alg2X inst y` its final primal vector — both computed from
the instance and the arrival order alone. The retired version took `y` as a free vector pinned
only by final covering feasibility, which admits inflated `y`. `hS` is the standing feasibility
assumption of the covering LP (every constraint involves at least one variable). Conclusions:
the covering solution is feasible (Claim (1)); the packing solution `y` is exactly feasible
(Claim (3), p. 122: non-negative and `∑_{j | i ∈ S(j)} yⱼ ≤ cᵢ`); the covering solution is
`2 ln(1+d)`-competitive against every feasible offline covering solution (Eq. (4.2),
`∂P/∂yⱼ ≤ 2 ln(1+d) · ∂D/∂yⱼ`, and weak duality); the packing solution is `2 ln(1+d)`-competitive
against every feasible offline packing solution. -/
theorem algorithm2_competitive_ratio_v2 {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    [DecidableEq J] (inst : CoveringInstance I J) (hS : ∀ j, (inst.S j).Nonempty)
    (ord : List J) (hord_nodup : ord.Nodup) (hord_mem : ∀ j, j ∈ ord) :
    let y : J → ℝ := raiseRun inst (alg2X inst) ord
    let x : I → ℝ := alg2X inst y
    (∀ j, 1 ≤ ∑ i ∈ inst.S j, x i) ∧
    ((∀ j, 0 ≤ y j) ∧ ∀ i : I, dualSum inst y i ≤ inst.c i) ∧
    (∀ x'' : I → ℝ, (∀ i, 0 ≤ x'' i) → (∀ j, 1 ≤ ∑ i ∈ inst.S j, x'' i) →
        ∑ i, inst.c i * x i ≤ 2 * Real.log (1 + inst.d) * ∑ i, inst.c i * x'' i) ∧
    (∀ y'' : J → ℝ, (∀ j, 0 ≤ y'' j) → (∀ i, dualSum inst y'' i ≤ inst.c i) →
        ∑ j, y'' j ≤ 2 * Real.log (1 + inst.d) * ∑ j, y j) := by sorry

end OnlinePrimalDual.Framework

