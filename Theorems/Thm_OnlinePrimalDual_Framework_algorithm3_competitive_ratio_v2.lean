import Mathlib
import Definitions.Def_OnlinePrimalDual_Framework_CoveringInstance
import Definitions.Def_OnlinePrimalDual_Framework_dualSum
import Definitions.Def_OnlinePrimalDual_Framework_alg3X
import Definitions.Def_OnlinePrimalDual_Framework_raiseRun_v2


namespace OnlinePrimalDual.Framework

/-- **Theorem 4.3** (Buchbinder & Naor, FnT TCS 2009, p. 124-126), Algorithm 3, the
complementary-slackness algorithm — the goal of this mission. `ord` is the online arrival order
of the covering constraints (a permutation of `J`); `y = raiseRun inst (alg3X inst) ord` is
Algorithm 3's own final dual vector (p. 124: each arriving `yⱼ` is increased continuously
*exactly while* `∑_{i ∈ S(j)} xᵢ < 1`, with `x` given by the closed form `alg3X` of steps
(1b)-(1c)), and `x = alg3X inst y` its final primal vector — both computed from the instance and
the arrival order alone. The retired version took `y` as a free vector pinned only by final
covering feasibility, which admits inflated `y`. `hS` is the standing feasibility assumption of
the covering LP (every constraint involves at least one variable). Conclusions, with the exact
constants the book's proof derives: the covering solution is feasible (Claim (1), p. 125); the
packing solution `y` is non-negative and violates each packing constraint by a factor of at most
`1 + ln d` (Claim (2), p. 125, "∑ yⱼ ≤ cᵢ(1 + ln d)"); the covering solution is
`2(1 + ln d)`-competitive against every feasible offline covering solution (Claim (3), `P ≤ 2D`,
p. 125-126, with the rescaled `y` and weak duality); the packing solution is `2`-competitive
against every feasible offline packing solution (`P ≤ 2D` and weak duality both ways). -/
theorem algorithm3_competitive_ratio_v2 {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    [DecidableEq J] (inst : CoveringInstance I J) (hS : ∀ j, (inst.S j).Nonempty)
    (ord : List J) (hord_nodup : ord.Nodup) (hord_mem : ∀ j, j ∈ ord) :
    let y : J → ℝ := raiseRun inst (alg3X inst) ord
    let x : I → ℝ := alg3X inst y
    (∀ j, 1 ≤ ∑ i ∈ inst.S j, x i) ∧
    ((∀ j, 0 ≤ y j) ∧ ∀ i : I, dualSum inst y i ≤ inst.c i * (1 + Real.log inst.d)) ∧
    (∀ x'' : I → ℝ, (∀ i, 0 ≤ x'' i) → (∀ j, 1 ≤ ∑ i ∈ inst.S j, x'' i) →
        ∑ i, inst.c i * x i ≤ 2 * (1 + Real.log inst.d) * ∑ i, inst.c i * x'' i) ∧
    (∀ y'' : J → ℝ, (∀ j, 0 ≤ y'' j) → (∀ i, dualSum inst y'' i ≤ inst.c i) →
        ∑ j, y'' j ≤ 2 * ∑ j, y j) := by sorry

end OnlinePrimalDual.Framework

