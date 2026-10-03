import Mathlib
import Definitions.Def_MDPFinance_StructuredModels_Model
import Definitions.Def_MDPFinance_StructuredModels_Policy
import Definitions.Def_MDPFinance_StructuredModels_Operators
import Definitions.Def_MDPFinance_StructuredModels_BoundingFunction
import Definitions.Def_MDPFinance_StructuredModels_StructureAssumption

open MeasureTheory ProbabilityTheory

namespace MDPFinance.StructuredModels

/-- Theorem 2.4.14 (Bäuerle–Rieder, p. 35, PDF 50). Suppose a Markov Decision Model with upper
bounding function `b` is given and for all `n = 0, …, N-1` it holds: (i) `D_n(·)` is increasing,
i.e. `x ≤ x'` implies `D_n(x) ⊂ D_n(x')`; (ii) the stochastic kernels `Q_n(·|x,a)` are
stochastically monotone for all `a ∈ D_n(x)`, i.e. `x ↦ ∫ v(x') Q_n(dx'|x,a)` is increasing for
all increasing `v ∈ IB_b^+` and for all `a ∈ D_n(x)`; (iii) `x ↦ r_n(x,a)` is increasing for all
`a`; (iv) `g_N` is increasing on `E`; (v) for all increasing `v ∈ IB_b^+` there exists a
maximizer `f_n ∈ Δ_n` of `v`. Then the sets `IM_n := {v ∈ IB_b^+ | v increasing}` and `Δ_n`
satisfy the Structure Assumption (SAN). In (ii) and (iii) the maps `x ↦ ∫ v dQ_n(·|x,a)` and
`x ↦ r_n(x,a)` are increasing on their domain `{x | a ∈ D_n(x)}` (an up-set by (i)), where `Q_n` and
`r_n` are defined. -/
theorem monotone_structure_theorem {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]
    [Preorder E] [Preorder A] {N : ℕ} (M : MarkovDecisionModel E A N) (b : E → ℝ)
    (cr cg αb : ℝ) (hb : IsUpperBoundingFunction M b cr cg αb) (Deltas : ℕ → Set (E → A))
    (hD : ∀ n < N, Monotone (M.Dx n))
    (hQ : ∀ n < N, ∀ a, ∀ v ∈ IBbPlus b, Monotone v →
      MonotoneOn (fun x' => erealIntegral (M.Q n (x', a)) v) {x' | a ∈ M.Dx n x'})
    (hr : ∀ n < N, ∀ a, MonotoneOn (fun x => M.r n (x, a)) {x | a ∈ M.Dx n x})
    (hg : Monotone M.g)
    (hmax : ∀ n < N, ∀ v ∈ IBbPlus b, Monotone v → ∃ f ∈ Deltas n, IsMaximizer M n v f) :
    StructureAssumption M (fun n => {v ∈ IBbPlus b | Monotone v}) Deltas := by sorry

end MDPFinance.StructuredModels
