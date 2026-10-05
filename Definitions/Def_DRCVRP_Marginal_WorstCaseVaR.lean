import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional

open MeasureTheory

namespace DRCVRP.Marginal

/-!
Ghosal and Wiesemann, *The Distributionally Robust Chance-Constrained Vehicle Routing Problem*,
Oper. Res. 68(3) (2020). Customers are `Fin n` (the paper's `V_C = {1,…,n}`, 0-based); a demand
vector is `q : Fin n → ℝ`, and distributions of the random demand vector are measures on
`Fin n → ℝ`.
-/

/-- The worst-case value-at-risk `sup_{ℙ ∈ 𝒫} ℙ-VaR_{1-ε}[∑_{i ∈ S} q̃_i]` of the total demand of
the customer set `S` over the ambiguity set `Amb` (p. 721, Eq. (2); p. 723, Theorem 3), with
`ℙ-VaR_{1-ε}[X̃] = inf {x ∈ ℝ : ℙ[X̃ ≤ x] ≥ 1 - ε}` (p. 720). The supremum is the real `sSup`
of the image of `Amb`; the single-customer value `sup_{ℙ ∈ 𝒫} ℙ-VaR_{1-ε}[q̃_i]` is
`worstCaseVaR Amb ε {i}`. -/
noncomputable def worstCaseVaR {n : ℕ} (Amb : Set (Measure (Fin n → ℝ))) (ε : ℝ)
    (S : Finset (Fin n)) : ℝ :=
  sSup ((fun P => MultistageStochastic.valueAtRisk P (fun q => ∑ i ∈ S, q i) (1 - ε)) '' Amb)

end DRCVRP.Marginal
