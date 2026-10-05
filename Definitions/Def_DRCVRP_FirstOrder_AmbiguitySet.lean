import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional

open MeasureTheory

namespace DRCVRP.FirstOrder

/-!
Ghosal and Wiesemann, *The Distributionally Robust Chance-Constrained Vehicle Routing Problem*,
Oper. Res. 68(3) (2020), §5.1, p. 725. Customers are `Fin n` (the paper's `V_C = {1,…,n}`,
0-based); a demand vector is `q : Fin n → ℝ`, and distributions of the random demand vector
`q̃` are measures on `Fin n → ℝ`. The customer subsets `S_1, …, S_p` are `Sfam : Fin p → Finset
(Fin n)` (0-based).
-/

/-- The first-order generic moment ambiguity set (12) (§5.1, p. 725):
`𝒫 = {ℙ ∈ 𝒫₀(ℝⁿ) : ℙ[q̃ ∈ 𝒬] = 1, 𝔼_ℙ[q̃] = μ, 𝔼_ℙ[1_{S_l}ᵀ |q̃ − μ|] ≤ ν_l ∀ l}` with the
rectangular support `𝒬 = [qlo, qhi]`, the mean vector `μ`, the customer subsets `Sfam l` and the
mean-absolute-deviation bounds `ν l`; `1_{S_l}ᵀ |q̃ − μ| = ∑_{j ∈ S_l} |q̃_j − μ_j|`.
The integrability clauses make the expectations genuine Bochner integrals; for a probability
measure carried by the box they hold automatically, so they do not shrink the set. -/
def firstOrderAmbiguitySet {n p : ℕ} (qlo qhi μ : Fin n → ℝ) (Sfam : Fin p → Finset (Fin n))
    (ν : Fin p → ℝ) : Set (Measure (Fin n → ℝ)) :=
  {P | IsProbabilityMeasure P ∧ P (Set.Icc qlo qhi) = 1 ∧
    (∀ j, Integrable (fun q => q j) P ∧ ∫ q, q j ∂P = μ j) ∧
    ∀ l, Integrable (fun q => ∑ j ∈ Sfam l, |q j - μ j|) P ∧
      ∫ q, (∑ j ∈ Sfam l, |q j - μ j|) ∂P ≤ ν l}

/-- The worst-case value-at-risk `sup_{ℙ ∈ 𝒫} ℙ-VaR_{1-ε}[∑_{i ∈ S} q̃_i]` of the cumulative
demand of the customer subset `S` over an ambiguity set `Amb` (the paper's `𝒫`) (§3, p. 721;
§5.1, p. 726, Theorem 5), with `ℙ-VaR_{1-ε}[X̃] = inf {x ∈ ℝ : ℙ[X̃ ≤ x] ≥ 1 - ε}` (p. 720).
The supremum is the real `sSup` of the image of `Amb`. -/
noncomputable def worstCaseVaR {n : ℕ} (Amb : Set (Measure (Fin n → ℝ))) (ε : ℝ)
    (S : Finset (Fin n)) : ℝ :=
  sSup ((fun P => MultistageStochastic.valueAtRisk P (fun q => ∑ i ∈ S, q i) (1 - ε)) '' Amb)

end DRCVRP.FirstOrder
