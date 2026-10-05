import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_DRCVRP_Marginal_WorstCaseVaR
import Definitions.Def_DRCVRP_Marginal_AmbiguitySets
import Definitions.Def_DRCVRP_Marginal_Routing

open MeasureTheory

namespace DRCVRP.Marginal

/-- Corollary 1 (Ghosal and Wiesemann 2020, §4, p. 723): over a marginalized moment ambiguity
set (5), a route set is feasible in RVRP(𝒫) if and only if it is feasible in the deterministic
CVRP with customer demands `q_i = sup_{ℙ ∈ 𝒫} ℙ-VaR_{1-ε}[q̃_i]`. Both problems minimize the same
cost `c(R)`, so they are equivalent. -/
theorem rvrp_marginal_iff_deterministic {n m : ℕ}
    (qlo qhi μ : Fin n → ℝ) (ε : ℝ) (hε₀ : 0 < ε) (hε₁ : ε < 1)
    (hqlo : ∀ i, 0 ≤ qlo i) (hμ : ∀ i, qlo i < μ i ∧ μ i < qhi i)
    {p : Fin n → ℕ} (φ : (i : Fin n) → Fin (p i) → ℝ → ℝ) (σ : (i : Fin n) → Fin (p i) → ℝ)
    (hφ : ∀ i l, ConvexOn ℝ Set.univ (φ i l)) (hσ : ∀ i l, φ i l (μ i) < σ i l)
    (Q : ℝ) (hQ : 0 ≤ Q) (R : Fin m → List (Fin n)) :
    RVRPFeasible (marginalSet qlo qhi μ φ σ) ε Q R ↔
      CVRPFeasible (fun i => worstCaseVaR (marginalSet qlo qhi μ φ σ) ε {i}) Q R := by sorry

end DRCVRP.Marginal

