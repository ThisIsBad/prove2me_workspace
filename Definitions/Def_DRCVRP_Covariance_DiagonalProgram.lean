import Mathlib

namespace DRCVRP.Covariance

/-!
The one-dimensional program (18) of Corollary 4 in Ghosal and Wiesemann, *The Distributionally
Robust Chance-Constrained Vehicle Routing Problem*, Oper. Res. 68(3) (2020), §5.2, p. 727, for a
diagonal covariance bound `Σ = diag(σ₁², …, σₙ²)`. Here `u : Fin n → ℝ` stands for the bound
`q^u` and `r` for `(1-ε)/ε`.
-/

/-- `S(θ) = {i ∈ S : σ_i² > θ · q^u_i}` (p. 727, below (18)). -/
noncomputable def capSet {n : ℕ} (u σ : Fin n → ℝ) (S : Finset (Fin n)) (θ : ℝ) : Finset (Fin n) :=
  S.filter (fun i => θ * u i < σ i ^ 2)

/-- The slack `(1-ε)/ε - ∑_{i ∈ S(θ)} (q^u_i/σ_i)²`, the first factor under the square root
of (18). -/
noncomputable def capSlack {n : ℕ} (u σ : Fin n → ℝ) (S : Finset (Fin n)) (r θ : ℝ) : ℝ :=
  r - ∑ i ∈ capSet u σ S θ, (u i / σ i) ^ 2

/-- The objective of (18) without the constant `1_Sᵀμ`:
`∑_{i ∈ S(θ)} q^u_i + √([(1-ε)/ε - ∑_{i ∈ S(θ)} (q^u_i/σ_i)²][∑_{i ∈ S∖S(θ)} σ_i²])`. -/
noncomputable def diagObjective {n : ℕ} (u σ : Fin n → ℝ) (S : Finset (Fin n)) (r θ : ℝ) : ℝ :=
  ∑ i ∈ capSet u σ S θ, u i +
    Real.sqrt (capSlack u σ S r θ * ∑ i ∈ S \ capSet u σ S θ, σ i ^ 2)

end DRCVRP.Covariance
