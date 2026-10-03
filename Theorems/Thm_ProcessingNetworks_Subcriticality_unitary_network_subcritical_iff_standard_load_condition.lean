import Mathlib
import Definitions.Def_ProcessingNetworks_Subcriticality_SPNPlanningData
import Definitions.Def_ProcessingNetworks_Subcriticality_StaticPlanningProblem

namespace ProcessingNetworks.Subcriticality

/-- Proposition 5.1, p. 94 (PDF p. 110): a unitary network is subcritical if and only if it
satisfies the standard load condition (5.1), `ρ < b`. `P` is the network's routing matrix,
substochastic (`hP_nonneg`, `hP_rowsum`) and transient (`hP_transient`, `Pⁿ → 0` entrywise, as in
Section 2.6); `α` is the throughput-rate vector solving `(1 - Pᵀ)α = λ` (Eq. (2.38)), and the load
vector is `ρ = A·diag(m)·α` (Eq. (2.40)), with `A`, `m`, `b` as usual; the arrival-rate vector
`λ ∈ ℝ^I_+` is nonnegative, as throughout (Section 5.3). -/
theorem unitary_network_subcritical_iff_standard_load_condition
    {I K : ℕ} (P : Matrix (Fin I) (Fin I) ℝ)
    (hP_nonneg : ∀ i j, 0 ≤ P i j) (hP_rowsum : ∀ i, ∑ j, P i j ≤ 1)
    (hP_transient : ∀ i j, Filter.Tendsto (fun n => (P ^ n) i j) Filter.atTop (nhds 0))
    (m : Fin I → ℝ) (hm : ∀ i, 0 < m i)
    (A : Matrix (Fin K) (Fin I) ℝ) (b : Fin K → ℝ) (hb : ∀ k, 0 < b k)
    (lam alpha : Fin I → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (halpha : (1 - P.transpose).mulVec alpha = lam) :
    lam ∈ SubcriticalRegion (SPNPlanningData.ofUnitary P m hm A b hb) ↔
      ∀ k, (A.mulVec ((Matrix.diagonal m).mulVec alpha)) k < b k := by sorry

end ProcessingNetworks.Subcriticality
