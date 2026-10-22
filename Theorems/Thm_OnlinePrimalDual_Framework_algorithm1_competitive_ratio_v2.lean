import Mathlib
import Definitions.Def_OnlinePrimalDual_Framework_CoveringInstance
import Definitions.Def_OnlinePrimalDual_Framework_dualSum
import Definitions.Def_OnlinePrimalDual_Framework_alg1Run_v2


namespace OnlinePrimalDual.Framework

/-- **Theorem 4.1** (Buchbinder & Naor, FnT TCS 2009, p. 118-120), Algorithm 1, the basic discrete
algorithm. `ord` is the online arrival order of the covering constraints (`hord_nodup`/`hord_mem`:
a permutation of `J`); `alg1Run inst ord` is Algorithm 1's own output (p. 118, steps (1a)-(1b)
applied verbatim: each arriving constraint is processed by inner-loop iterations *exactly while*
it is still violated, and `yⱼ` counts them), so `x` and `y` below are computed from the instance
and the arrival order alone — the retired version let the iteration counts be a free variable
pinned only by final feasibility, which admits over-incremented runs. `hc1` is the book's standing
assumption `cᵢ ≥ 1` for this algorithm (p. 118); `hS` is the standing feasibility assumption of the
covering LP (every constraint involves at least one variable; otherwise the book's loop never
terminates). Conclusions: the covering solution is feasible (Claim (1), part of "produces a
covering solution"); the integral packing solution `y` violates each packing constraint by a
factor of at most `log₂(3d+1)` (Claims (2)-(3) with the proof's own displayed bound, p. 120); the
covering solution is `2·log₂(3d+1)`-competitive against every feasible offline covering solution;
the packing solution is `2`-competitive against every feasible offline packing solution
(`P ≤ 2D` and weak duality both ways). -/
theorem algorithm1_competitive_ratio_v2 {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    [DecidableEq J] (inst : CoveringInstance I J) (hc1 : ∀ i, 1 ≤ inst.c i)
    (hS : ∀ j, (inst.S j).Nonempty) (ord : List J)
    (hord_nodup : ord.Nodup) (hord_mem : ∀ j, j ∈ ord) :
    let x : I → ℝ := (alg1Run inst ord).1
    let y : J → ℝ := fun j => ((alg1Run inst ord).2 j : ℝ)
    (∀ j, 1 ≤ ∑ i ∈ inst.S j, x i) ∧
    (∀ i : I, dualSum inst y i ≤ inst.c i * Real.logb 2 (3 * inst.d + 1)) ∧
    (∀ x'' : I → ℝ, (∀ i, 0 ≤ x'' i) → (∀ j, 1 ≤ ∑ i ∈ inst.S j, x'' i) →
        ∑ i, inst.c i * x i ≤ 2 * Real.logb 2 (3 * inst.d + 1) * ∑ i, inst.c i * x'' i) ∧
    (∀ y'' : J → ℝ, (∀ j, 0 ≤ y'' j) → (∀ i, dualSum inst y'' i ≤ inst.c i) →
        ∑ j, y'' j ≤ 2 * ∑ j, y j) := by sorry

end OnlinePrimalDual.Framework

