import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_DRCVRP_FirstOrder_AmbiguitySet
import Definitions.Def_DRCVRP_FirstOrder_ConvexProgram

open MeasureTheory

namespace DRCVRP.FirstOrder

/-- Corollary 3 (§5.1, pp. 726–727, Eq. (15)): with `p = n + 1`, `S_i = {i}` for every customer
`i` and `S_{n+1} = V_C`, the worst-case value-at-risk over (12) is
`1_Sᵀ μ + min {ν_{n+1}/(2ε), ∑_{i∈S} min {q̂_i, ν_i/(2ε)}}`. -/
theorem worstCaseVaR_singletons {n : ℕ} (qlo qhi μ : Fin n → ℝ)
    (Sfam : Fin (n + 1) → Finset (Fin n)) (ν : Fin (n + 1) → ℝ) (ε : ℝ)
    (hqlo : ∀ j, 0 ≤ qlo j) (hμ : ∀ j, qlo j < μ j ∧ μ j < qhi j) (hν : ∀ l, 0 < ν l)
    (hε₀ : 0 < ε) (hε₁ : ε < 1)
    (hsing : ∀ i : Fin n, Sfam i.castSucc = {i})
    (hlast : Sfam (Fin.last n) = Finset.univ) (S : Finset (Fin n)) :
    worstCaseVaR (firstOrderAmbiguitySet qlo qhi μ Sfam ν) ε S =
      ∑ j ∈ S, μ j +
        min (ν (Fin.last n) / (2 * ε))
          (∑ i ∈ S, min (qhat qlo qhi μ ε i) (ν i.castSucc / (2 * ε))) := by sorry

end DRCVRP.FirstOrder

