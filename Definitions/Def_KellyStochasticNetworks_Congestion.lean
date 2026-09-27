import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop

namespace KellyStochasticNetworks

/-- The feasible flow vectors of the network problem `network(A, C; w)` of section 7.1:
non-negative route rates whose induced link loads respect the capacities. -/
def networkFeasible {J R : ℕ} (A : Fin J → Fin R → ℝ) (C : Fin J → ℝ) : Set (Fin R → ℝ) :=
  {x | (∀ r, 0 ≤ x r) ∧ ∀ j, linkFlow A x j ≤ C j}

/-- The objective `∑_r w_r log x_r` of `network(A, C; w)`. -/
noncomputable def networkObjective {R : ℕ} (w x : Fin R → ℝ) : ℝ :=
  ∑ r, w r * Real.log (x r)

/-- The utility `U(x) = ∑_r w_r log x_r - ∑_j ∫_0^{y_j} p_j(y) dy` of Theorem 7.6, where
`y_j = ∑_{s : j ∈ s} x_s` is the load on resource `j`. -/
noncomputable def primalUtility {J R : ℕ} (A : Fin J → Fin R → ℝ) (w : Fin R → ℝ)
    (p : Fin J → ℝ → ℝ) (x : Fin R → ℝ) : ℝ :=
  (∑ r, w r * Real.log (x r)) - ∑ j, ∫ y in (0:ℝ)..(linkFlow A x j), p j y

/-- The right-hand side of the **primal algorithm** (7.5)–(7.6):
`κ_r (w_r - x_r ∑_{j ∈ r} p_j(∑_{s : j ∈ s} x_s))`. -/
noncomputable def primalDrift {J R : ℕ} (A : Fin J → Fin R → ℝ) (w κ : Fin R → ℝ)
    (p : Fin J → ℝ → ℝ) (x : Fin R → ℝ) (r : Fin R) : ℝ :=
  κ r * (w r - x r * ∑ j, A j r * p j (linkFlow A x j))

end KellyStochasticNetworks
