import Mathlib

open MeasureTheory

namespace DRCVRP.Covariance

/-!
The route-set layer of Ghosal and Wiesemann, *The Distributionally Robust Chance-Constrained
Vehicle Routing Problem*, Oper. Res. 68(3) (2020), §2, pp. 718–719, as far as feasibility is
concerned (costs are not needed). Customers are `Fin n` (0-based), vehicles `Fin m`.
-/

/-- `R ∈ 𝔓(V_C, m)` (p. 718): `R = (R_1, …, R_m)` is an ordered partition of the customers into
`m` nonempty ordered routes; every customer occurs exactly once across all routes. -/
def IsRouteSet {n m : ℕ} (R : Fin m → List (Fin n)) : Prop :=
  (∀ k, R k ≠ []) ∧ List.Perm (List.ofFn R).flatten (List.finRange n)

/-- Feasibility in the distributionally robust CVRP RVRP(𝒫) (p. 719): `R ∈ 𝔓(V_C, m)` and
`ℙ[∑_{i ∈ R_k} q̃_i ≤ Q] ≥ 1 - ε` for every `ℙ ∈ 𝒫` and every vehicle `k`. -/
def RVRPFeasible {n m : ℕ} (Amb : Set (Measure (Fin n → ℝ))) (ε Q : ℝ)
    (R : Fin m → List (Fin n)) : Prop :=
  IsRouteSet R ∧ ∀ k, ∀ P ∈ Amb, ENNReal.ofReal (1 - ε) ≤ P {q | ((R k).map q).sum ≤ Q}

/-- Feasibility in the deterministic CVRP with vehicle capacity `Q` and demands `q` (p. 719):
`R ∈ 𝔓(V_C, m)` and `R_k ∈ ℛ(q)`, i.e. `∑_{i ∈ R_k} q_i ≤ Q`, for every vehicle `k`. -/
def DetFeasible {n m : ℕ} (Q : ℝ) (q : Fin n → ℝ) (R : Fin m → List (Fin n)) : Prop :=
  IsRouteSet R ∧ ∀ k, ((R k).map q).sum ≤ Q

end DRCVRP.Covariance
