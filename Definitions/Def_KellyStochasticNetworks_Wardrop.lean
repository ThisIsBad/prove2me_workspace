import Mathlib

namespace KellyStochasticNetworks

/-- The flow on link `j` induced by the route flows `x` and the link-route incidence matrix `A`:
`y_j = ∑_r A_{jr} x_r`.  Kelly–Yudovina, *Stochastic Networks*, p. 94. -/
def linkFlow {J R : ℕ} (A : Fin J → Fin R → ℝ) (x : Fin R → ℝ) (j : Fin J) : ℝ :=
  ∑ r, A j r * x r

/-- The feasible route flows: non-negative, and carrying exactly `f σ` between each
source-destination pair `σ`.  The map `s` sends a route to the source-destination pair it
serves, which is the book's incidence matrix `H` (whose column sums are `1`). -/
def wardropFeasible {R Sd : ℕ} (s : Fin R → Fin Sd) (f : Fin Sd → ℝ) : Set (Fin R → ℝ) :=
  {x | (∀ r, 0 ≤ x r) ∧ ∀ σ, (∑ r ∈ Finset.univ.filter (fun r => s r = σ), x r) = f σ}

/-- **Wardrop equilibrium**, Definition 4.2: a feasible vector of route flows such that every
route carrying positive traffic has minimal delay among the routes serving the same
source-destination pair.  The delay on route `r` is `∑_j D_j(y_j) A_{jr}`, the sum of the link
delays along it. -/
def IsWardropEquilibrium {J R Sd : ℕ} (A : Fin J → Fin R → ℝ) (s : Fin R → Fin Sd)
    (D : Fin J → ℝ → ℝ) (f : Fin Sd → ℝ) (x : Fin R → ℝ) : Prop :=
  x ∈ wardropFeasible s f ∧
    ∀ r r' : Fin R, s r' = s r → 0 < x r →
      (∑ j, D j (linkFlow A x j) * A j r) ≤ ∑ j, D j (linkFlow A x j) * A j r'

/-- The objective `∑_j ∫_0^{y_j} D_j(u) du` of the optimization problem in the proof of
Theorem 4.3. -/
noncomputable def wardropObjective {J R : ℕ} (A : Fin J → Fin R → ℝ) (D : Fin J → ℝ → ℝ)
    (x : Fin R → ℝ) : ℝ :=
  ∑ j, ∫ u in (0:ℝ)..(linkFlow A x j), D j u

/-- The mean cost per unit time `W(ν; φ)` of the queueing network of section 4.3.1: a customer
on route `r` costs `w_r` per unit delay, and the mean sojourn time at queue `j` is
`1/(φ_j - λ_j)` with `λ_j = ∑_{r : j ∈ r} ν_r`. -/
noncomputable def queueingCost {J R : ℕ} (A : Fin J → Fin R → ℝ) (w ν : Fin R → ℝ)
    (φ : Fin J → ℝ) : ℝ :=
  ∑ r, w r * ∑ j, A j r * (ν r / (φ j - ∑ r', A j r' * ν r'))

/-- Braess's paradox, Figure 4.4a: links `S→W`, `W→N`, `S→E`, `E→N` and the two routes
`{S→W, W→N}` and `{S→E, E→N}`. -/
def braessIncidenceA : Fin 4 → Fin 2 → ℝ := ![![1, 0], ![1, 0], ![0, 1], ![0, 1]]

/-- The link delays of Figure 4.4a: `10y` on `S→W` and `E→N`, `y + 50` on `W→N` and `S→E`. -/
noncomputable def braessDelayA : Fin 4 → ℝ → ℝ :=
  ![fun y => 10 * y, fun y => y + 50, fun y => y + 50, fun y => 10 * y]

/-- Braess's paradox, Figure 4.4b: the same network with the extra road `W→E` added, and the
third route `{S→W, W→E, E→N}` it creates. -/
def braessIncidenceB : Fin 5 → Fin 3 → ℝ :=
  ![![1, 0, 1], ![1, 0, 0], ![0, 1, 0], ![0, 1, 1], ![0, 0, 1]]

/-- The link delays of Figure 4.4b: those of Figure 4.4a together with `y + 10` on the new
road `W→E`. -/
noncomputable def braessDelayB : Fin 5 → ℝ → ℝ :=
  ![fun y => 10 * y, fun y => y + 50, fun y => y + 50, fun y => 10 * y, fun y => y + 10]

end KellyStochasticNetworks
