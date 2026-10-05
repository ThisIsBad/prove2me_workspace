import Mathlib
import Definitions.Def_StochasticProg_Recourse_Instance
import Definitions.Def_StochasticProg_LShaped_Bases
import Definitions.Def_StochasticProg_LShaped_Algorithm

namespace StochasticProg.LShaped

open StochasticProg.Recourse

variable {n1 n2 m1 m2 K : ℕ}

/-- Chapter 5, Theorem 2 (p. 198): "When `ξ` is a finite random variable, the L-shaped
algorithm finitely converges to an optimal solution when it exists or proves the
infeasibility of Problem (3.1.2), namely, `min cᵀx + Q(x) s.t. x ∈ K1 ∩ K2`."

Formalized as: starting from no cuts at all, some run of the algorithm's Step-1-2-3
transition (`Step`) — one that takes optimal simplex bases, as the book's Steps 2–3 do — reaches, within a number of steps bounded by the finite total number of
feasibility- and optimality-cut witnesses available (`Fintype.card (Fin K × FeasBasis n2
m2) + Fintype.card (Fin K → Basis n2 m2)` — "there is only a finite number of different
combinations of the `K` multipliers ... because each corresponds to one of the finitely
many different bases", p. 220), a state from which no further `Step` cut can be added,
i.e. either the master problem has become infeasible (certifying `K1 ∩ K2 = ∅`) or its
optimum `x` is second-stage feasible, satisfies every fresh Step-3 termination test, and is
optimal for Problem (3.1.2).

v2 (2026-10-05): the published statement was disproved (an unbounded instance has neither an optimum nor infeasibility). This version adds three hypotheses. Every realization has positive probability (`hp_pos`): §5.1, p. 182, "k = 1, ..., K index its possible realizations". `W` has full row rank (`hW`), which the proof's "bases of (1.5)" and "simplex multipliers" (p. 197) presuppose. `K1` is bounded (`hK1`): not stated in the book, but a sufficient condition for what Step 1 takes for granted ("let (x^ν, θ^ν) be an optimal solution", p. 183); with it "an optimal solution when it exists" is automatic. The run is existential: the `Step` relation also admits bases that only attain the value without being dual feasible, so "every run" would be false. -/
theorem thm2_finite_convergence_v2 (inst : Instance n1 n2 m1 m2 K)
    (hp_pos : ∀ k, 0 < inst.p k)            -- §5.1: k indexes the possible realizations
    (hW : inst.W.rank = m2)                  -- (1.5) has bases / simplex multipliers
    (hK1 : Bornology.IsBounded (K1 inst)) :  -- Step 1's master LP has an optimal solution
    ∃ (N : ℕ) (path : ℕ → State inst),
      N ≤ Fintype.card (Fin K × FeasBasis n2 m2) + Fintype.card (Fin K → Basis n2 m2) ∧
      path 0 = (∅, ∅) ∧
      (∀ i, i < N → Step inst (path i) (path (i + 1))) ∧
      (∀ Sf' So', ¬ Step inst (path N) (Sf', So')) ∧
      ((IsMasterInfeasible inst (path N).1 ∧ K1 inst ∩ K2 inst = ∅) ∨
        (∃ x θ, IsMasterOptimal inst (path N).1 (path N).2 x θ ∧
          x ∈ K1 inst ∩ K2 inst ∧
          (∀ β, IsOptimalAt inst x β →
            θ ≥ (optCutCoeffs inst β).2 - dotProduct (optCutCoeffs inst β).1 x) ∧
          ∀ x' ∈ K1 inst ∩ K2 inst, obj inst x ≤ obj inst x')) := by
  sorry

end StochasticProg.LShaped

