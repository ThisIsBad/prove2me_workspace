import Mathlib
import Definitions.Def_PoissonDirichlet_Wendel_Setting
open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.Wendel

/-- (34), second equality, p. 863: for 0 < α < 1 and λ ≥ 0,
`ψ_α(λ) = Γ(1 - α) λ^α + φ_α(λ)`. -/
theorem eq_34 (α : ℝ) (hα : 0 < α) (hα1 : α < 1) (l : ℝ) (hl : 0 ≤ l) :
    psi α l = Real.Gamma (1 - α) * l ^ α + phi α l := by sorry

end PoissonDirichlet.Wendel

