import Mathlib
import Definitions.Def_OnlinePrimalDual_Framework_CoveringInstance

namespace OnlinePrimalDual.Framework

/-- One pass of the inner loop of Algorithm 1 (Buchbinder & Naor, *The Design of Competitive
Online Algorithms via a Primal-Dual Approach*, FnT TCS 2009, p. 118, step (1a)) while the
covering constraint `j` is being processed: every primal variable `i ∈ S(j)` is updated by
`xᵢ ← xᵢ(1 + 1/cᵢ) + 1/(|S(j)|·cᵢ)`, with the round's own `|S(j)| = (inst.S j).card`; variables
outside `S(j)` are untouched. -/
noncomputable def alg1Step {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (inst : CoveringInstance I J) (j : J) (x : I → ℝ) : I → ℝ :=
  fun i => if i ∈ inst.S j then x i * (1 + 1 / inst.c i) + 1 / ((inst.S j).card * inst.c i)
    else x i

/-- The number of inner-loop iterations Algorithm 1 performs on constraint `j` when it arrives
with the primal vector `x` in hand: the loop "while `∑_{i ∈ S(j)} xᵢ < 1`" (p. 118) runs exactly
until the constraint is satisfied, so this is the least `k` with
`1 ≤ ∑_{i ∈ S(j)} (alg1Step inst j)^[k] x i`; it is also the integral value the algorithm gives
to the dual variable `yⱼ` (step (1b), `yⱼ ← yⱼ + 1` once per iteration, starting from `0`).
`sInf` on `ℕ` returns `0` when no such `k` exists; this happens only for `S(j) = ∅` (then the
covering LP is infeasible and the book's loop never terminates), a case the theorems exclude by
the standing feasibility assumption `∀ j, (inst.S j).Nonempty`. -/
noncomputable def alg1Count {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (inst : CoveringInstance I J) (j : J) (x : I → ℝ) : ℕ :=
  sInf {k : ℕ | 1 ≤ ∑ i ∈ inst.S j, (alg1Step inst j)^[k] x i}

/-- The complete run of Algorithm 1 (p. 118) on the instance `inst`, the covering constraints
arriving in the order `ord : List J` (one entry per constraint): starting from `x = 0`, `y = 0`,
each arriving constraint `j` is processed by `alg1Count inst j x` inner-loop iterations, after
which `x` has been updated that many times by `alg1Step inst j` and `yⱼ` equals that count.
The result is the pair (final primal/covering vector, final integral dual/packing vector) the
algorithm outputs, as a function of the instance and the arrival order only. -/
noncomputable def alg1Run {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (inst : CoveringInstance I J) (ord : List J) : (I → ℝ) × (J → ℕ) :=
  ord.foldl
    (fun st j =>
      ((alg1Step inst j)^[alg1Count inst j st.1] st.1,
        Function.update st.2 j (alg1Count inst j st.1)))
    (fun _ => 0, fun _ => 0)

end OnlinePrimalDual.Framework
