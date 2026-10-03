import Mathlib
import Definitions.Def_MDPFinance_StructuredModels_Model
import Definitions.Def_MDPFinance_StructuredModels_Policy
import Definitions.Def_MDPFinance_StructuredModels_Operators
import Definitions.Def_MDPFinance_StructuredModels_BoundingFunction
import Definitions.Def_MDPFinance_StructuredModels_StructureAssumption
import Definitions.Def_MDPFinance_StructuredModels_ConvexAnalysis

open MeasureTheory ProbabilityTheory

namespace MDPFinance.StructuredModels

/-- Theorem 2.4.22 (Bäuerle–Rieder, p. 38, PDF 53) — the goal of this mission. Suppose a Markov
Decision Model with upper bounding function `b` is given and for all `n = 0, …, N-1` it holds:
(i) `E` is convex and `D_n := E × A`; (ii) for all convex `v ∈ IB_b^+`, `x ↦ ∫ v(x') Q_n(dx'|x,a)`
is convex for all `a ∈ A`; (iii) `x ↦ r_n(x,a)` is convex for all `a ∈ A`; (iv) `g_N` is convex;
(v) for all convex `v ∈ IB_b^+` there exists a maximizer `f_n ∈ Δ_n` of `v`. Then the sets
`IM_n := {v ∈ IB_b^+ | v convex}` and `Δ_n` satisfy the Structure Assumption (SAN). -/
theorem convex_structure_theorem {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]
    [AddCommGroup E] [Module ℝ E] [AddCommGroup A] [Module ℝ A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (b : E → ℝ) (cr cg αb : ℝ)
    (hb : IsUpperBoundingFunction M b cr cg αb) (Deltas : ℕ → Set (E → A))
    (hEconvex : Convex ℝ (Set.univ : Set E))
    (hDn : ∀ n < N, M.D n = Set.univ)
    (hQ_convex : ∀ n < N, ∀ v ∈ IBbPlus b, ConvexOnEReal Set.univ v →
      ∀ a : A, ConvexOnEReal Set.univ (fun x => erealIntegral (M.Q n (x, a)) v))
    (hr_convex : ∀ n < N, ∀ a : A, ConvexOn ℝ Set.univ (fun x => M.r n (x, a)))
    (hg_convex : ConvexOn ℝ Set.univ M.g)
    (hmax : ∀ n < N, ∀ v ∈ IBbPlus b, ConvexOnEReal Set.univ v →
      ∃ f ∈ Deltas n, IsMaximizer M n v f) :
    StructureAssumption M (fun n => {v ∈ IBbPlus b | ConvexOnEReal Set.univ v}) Deltas := by sorry

end MDPFinance.StructuredModels
