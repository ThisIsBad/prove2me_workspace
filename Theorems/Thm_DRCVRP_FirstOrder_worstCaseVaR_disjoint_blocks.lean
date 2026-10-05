import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_DRCVRP_FirstOrder_AmbiguitySet
import Definitions.Def_DRCVRP_FirstOrder_ConvexProgram

open MeasureTheory

namespace DRCVRP.FirstOrder

/-- Corollary 2 (§5.1, p. 726, Eq. (14)): with `p = r + 1` subsets, the first `r` pairwise
disjoint and covering all customers and the last one equal to all customers, the worst-case
value-at-risk over (12) is `1_Sᵀ μ + min {ν_p/(2ε), ∑_{i<p} min {1_{S∩S_i}ᵀ q̂, ν_i/(2ε)}}`. -/
theorem worstCaseVaR_disjoint_blocks {n r : ℕ} (qlo qhi μ : Fin n → ℝ)
    (Sfam : Fin (r + 1) → Finset (Fin n)) (ν : Fin (r + 1) → ℝ) (ε : ℝ)
    (hqlo : ∀ j, 0 ≤ qlo j) (hμ : ∀ j, qlo j < μ j ∧ μ j < qhi j) (hν : ∀ l, 0 < ν l)
    (hε₀ : 0 < ε) (hε₁ : ε < 1)
    (hdisj : ∀ i i' : Fin r, i ≠ i' → Disjoint (Sfam i.castSucc) (Sfam i'.castSucc))
    (hcover : ∀ c : Fin n, ∃ i : Fin r, c ∈ Sfam i.castSucc)
    (hlast : Sfam (Fin.last r) = Finset.univ) (S : Finset (Fin n)) :
    worstCaseVaR (firstOrderAmbiguitySet qlo qhi μ Sfam ν) ε S =
      ∑ j ∈ S, μ j +
        min (ν (Fin.last r) / (2 * ε))
          (∑ i : Fin r,
            min (∑ j ∈ S ∩ Sfam i.castSucc, qhat qlo qhi μ ε j) (ν i.castSucc / (2 * ε))) := by sorry

end DRCVRP.FirstOrder

