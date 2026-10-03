import Mathlib
import Definitions.Def_MDPFinance_StructuredModels_Model
import Definitions.Def_MDPFinance_StructuredModels_Policy
import Definitions.Def_MDPFinance_StructuredModels_Operators
import Definitions.Def_MDPFinance_StructuredModels_BoundingFunction
import Definitions.Def_MDPFinance_StructuredModels_StructureAssumption
import Definitions.Def_MDPFinance_StructuredModels_ConvexAnalysis

open MeasureTheory ProbabilityTheory

namespace MDPFinance.StructuredModels

/-- Theorem 2.4.19 (Bäuerle–Rieder, p. 36, PDF 52). Suppose a Markov Decision Model with upper
bounding function `b` is given and for all `n = 0, …, N-1` it holds: (i) `D_n` is convex in
`E × A`; (ii) the mapping `(x,a) ↦ ∫ v(x') Q_n(dx'|x,a)` is concave for all concave `v ∈ IB_b^+`;
(iii) `(x,a) ↦ r_n(x,a)` is concave; (iv) `g_N` is concave on `E`; (v) for all concave
`v ∈ IB_b^+` there exists a maximizer `f_n ∈ Δ_n` of `v`. Then the sets
`IM_n := {v ∈ IB_b^+ | v concave}` and `Δ_n` satisfy the Structure Assumption (SAN). -/
theorem concave_structure_theorem {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]
    [AddCommGroup E] [Module ℝ E] [AddCommGroup A] [Module ℝ A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (b : E → ℝ) (cr cg αb : ℝ)
    (hb : IsUpperBoundingFunction M b cr cg αb) (Deltas : ℕ → Set (E → A))
    (hD_convex : ∀ n < N, Convex ℝ (M.D n))
    (hQ_concave : ∀ n < N, ∀ v ∈ IBbPlus b, ConcaveOnEReal Set.univ v →
      ConcaveOnEReal (M.D n) (fun xa => erealIntegral (M.Q n xa) v))
    (hr_concave : ∀ n < N, ConcaveOn ℝ (M.D n) (M.r n))
    (hg_concave : ConcaveOn ℝ Set.univ M.g)
    (hmax : ∀ n < N, ∀ v ∈ IBbPlus b, ConcaveOnEReal Set.univ v →
      ∃ f ∈ Deltas n, IsMaximizer M n v f) :
    StructureAssumption M (fun n => {v ∈ IBbPlus b | ConcaveOnEReal Set.univ v}) Deltas := by sorry

end MDPFinance.StructuredModels
