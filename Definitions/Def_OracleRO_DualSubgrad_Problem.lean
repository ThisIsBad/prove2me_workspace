import Mathlib

namespace OracleRO.DualSubgrad

/-- The robust feasibility problem (3) (p. 4) is feasible: some `x ∈ 𝒟` satisfies
`f i x u ≤ 0` for every constraint `i` and every `u ∈ 𝒰`. -/
def RobustFeasible {m n d : ℕ} (Dom : Set (EuclideanSpace ℝ (Fin n)))
    (U : Set (EuclideanSpace ℝ (Fin d)))
    (f : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ∃ x ∈ Dom, ∀ i, ∀ u ∈ U, f i x u ≤ 0

/-- `x` is an `ε`-approximate solution of problem (3) (p. 4): `x ∈ 𝒟` and
`f i x u ≤ ε` for every constraint `i` and every `u ∈ 𝒰`. -/
def IsApproxSolution {m n d : ℕ} (Dom : Set (EuclideanSpace ℝ (Fin n)))
    (U : Set (EuclideanSpace ℝ (Fin d)))
    (f : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d) → ℝ) (ε : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  x ∈ Dom ∧ ∀ i, ∀ u ∈ U, f i x u ≤ ε

/-- The `ε`-approximate optimization oracle `O_ε` of Figure 1 (p. 6). On every noise vector
`u = (u₁, …, u_m)` with each `uᵢ ∈ 𝒰`, the answer `O u = some x` is a point `x ∈ 𝒟` with
`f i x (u i) ≤ ε` for all `i`, and the answer `O u = none` ("infeasible") is given only when
no `x ∈ 𝒟` satisfies `f i x (u i) ≤ 0` for all `i`. -/
def IsApproxOracle {m n d : ℕ} (Dom : Set (EuclideanSpace ℝ (Fin n)))
    (U : Set (EuclideanSpace ℝ (Fin d)))
    (f : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d) → ℝ) (ε : ℝ)
    (O : (Fin m → EuclideanSpace ℝ (Fin d)) → Option (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ u : Fin m → EuclideanSpace ℝ (Fin d), (∀ i, u i ∈ U) →
    (∀ x, O u = some x → x ∈ Dom ∧ ∀ i, f i x (u i) ≤ ε) ∧
    (O u = none → ¬ ∃ x ∈ Dom, ∀ i, f i x (u i) ≤ 0)

end OracleRO.DualSubgrad
