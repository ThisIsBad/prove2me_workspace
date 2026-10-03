import Mathlib

namespace Disjunctive.RayCGLP

/-- `(CGLP)_y`, eq. (10.9) (Balas §10.6, p. 138): the cut-generating LP under the ray
normalization `αy=1`, for the fixed disjunctive hull `P_D`. Feasibility of `(α,β)` is stated
directly as validity for `P_D` (rather than through an explicit multiplier representation), since
Theorem 10.2/10.3/Corollary 10.4 are stated purely in terms of `(α,β)`-validity for `P_D`, matching
the book's own framing of `(CGLP)_y`'s feasible region as (a normalization slice of) the reverse
polar of `P_D`. -/
def IsCGLPYFeasible {n : ℕ} (PD : Set (Fin n → ℝ)) (y : Fin n → ℝ) (α : Fin n → ℝ) (β : ℝ) :
    Prop :=
  (∀ x ∈ PD, β ≤ dotProduct α x) ∧ dotProduct α y = 1

/-- `(CGLP)_y` has a finite minimum of its objective `αx̄-β`: the objective is bounded below over
the feasible region (Balas §10.6, p. 138, discussed just before Theorem 10.2). -/
def CGLPYHasFiniteMin {n : ℕ} (PD : Set (Fin n → ℝ)) (y : Fin n → ℝ) (xbar : Fin n → ℝ) : Prop :=
  BddBelow ((fun p : (Fin n → ℝ) × ℝ => dotProduct p.1 xbar - p.2) ''
    {p : (Fin n → ℝ) × ℝ | IsCGLPYFeasible PD y p.1 p.2})

/-- `(α,β)` is an optimal solution to `(CGLP)_y` (Balas §10.6, p. 138, Theorem 10.3): feasible,
and minimizing the objective `αx̄-β` over the feasible region. -/
def IsCGLPYOptimal {n : ℕ} (PD : Set (Fin n → ℝ)) (y : Fin n → ℝ) (xbar : Fin n → ℝ)
    (α : Fin n → ℝ) (β : ℝ) : Prop :=
  IsCGLPYFeasible PD y α β ∧
    ∀ α' β', IsCGLPYFeasible PD y α' β' → dotProduct α xbar - β ≤ dotProduct α' xbar - β'

end Disjunctive.RayCGLP
