import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional

open MeasureTheory

namespace DRCVRP.Covariance

/-!
The covariance ambiguity set and the worst-case value-at-risk of Ghosal and Wiesemann,
*The Distributionally Robust Chance-Constrained Vehicle Routing Problem*, Oper. Res. 68(3)
(2020), §5.2, p. 727, Eq. (16), and the bounds `q^ℓ`, `q^u` of Theorem 7 (p. 727).

Customers are `Fin n` (the paper's `V_C = {1, …, n}`, 0-based). A demand vector is
`q : Fin n → ℝ`; distributions are measures on `Fin n → ℝ`. The covariance bound `Σ` is
written `Sig`.
-/

/-- The second-moment matrix of `P` centred at `μ`, `𝔼_ℙ[(q̃ - μ)(q̃ - μ)ᵀ]`, entry `(i, j)`
equal to `∫ (q_i - μ_i)(q_j - μ_j) dℙ`. -/
noncomputable def centredSecondMoment {n : ℕ} (μ : Fin n → ℝ) (P : Measure (Fin n → ℝ)) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ∫ q, (q i - μ i) * (q j - μ j) ∂P

/-- The covariance ambiguity set (16), p. 727:
`𝒫 = {ℙ ∈ 𝒫₀(ℝⁿ) : ℙ[q̃ ∈ 𝒬] = 1, 𝔼_ℙ[q̃] = μ, 𝔼_ℙ[(q̃ - μ)(q̃ - μ)ᵀ] ⪯ Σ}` with the box support
`𝒬 = [q̲, q̄]`. The Loewner order `A ⪯ Σ` is `Σ - A` positive semidefinite. The side conditions
of (16) (`q̲ ≥ 0`, `μ ∈ int 𝒬`, `Σ ≻ 0`) are hypotheses of the theorems. -/
def covarianceSet {n : ℕ} (qlo qhi μ : Fin n → ℝ) (Sig : Matrix (Fin n) (Fin n) ℝ) :
    Set (Measure (Fin n → ℝ)) :=
  {P | IsProbabilityMeasure P ∧ P (Set.Icc qlo qhi) = 1 ∧ (∀ j, ∫ q, q j ∂P = μ j) ∧
    (Sig - centredSecondMoment μ P).PosSemidef}

/-- The worst-case value-at-risk `sup_{ℙ ∈ 𝒫} ℙ-VaR_{1-ε}[∑_{i ∈ S} q̃_i]` of the total demand of
the customer set `S`, with `ℙ-VaR_{1-ε}[X̃] = inf {x : ℙ[X̃ ≤ x] ≥ 1 - ε}` (p. 720). -/
noncomputable def worstCaseVaR {n : ℕ} (Amb : Set (Measure (Fin n → ℝ))) (ε : ℝ)
    (S : Finset (Fin n)) : ℝ :=
  sSup ((fun P => MultistageStochastic.valueAtRisk P (fun q => ∑ i ∈ S, q i) (1 - ε)) '' Amb)

/-- The lower bound of (17), p. 727: `q^ℓ = max{-((1-ε)/ε)(q̄ - μ), q̲ - μ}`, componentwise. -/
noncomputable def qLower {n : ℕ} (qlo qhi μ : Fin n → ℝ) (ε : ℝ) (j : Fin n) : ℝ :=
  max (-((1 - ε) / ε * (qhi j - μ j))) (qlo j - μ j)

/-- The upper bound of (17) and (18), p. 727: `q^u = min{((1-ε)/ε)(μ - q̲), q̄ - μ}`,
componentwise. -/
noncomputable def qUpper {n : ℕ} (qlo qhi μ : Fin n → ℝ) (ε : ℝ) (j : Fin n) : ℝ :=
  min ((1 - ε) / ε * (μ j - qlo j)) (qhi j - μ j)

end DRCVRP.Covariance
