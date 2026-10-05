import Mathlib
import Definitions.Def_EmmonsTardiness_EDD_Model

namespace EmmonsTardiness.EDD

/-- Emmons 1969, p. 713, Corollary 2.2*: for a loss function `g` convex and nondecreasing on
`[0, ∞)`, the EDD schedule is optimal for `Σ_J g(T_i)` if it produces starting times
`W_i ≤ d_i` for all `i`. -/
theorem corollary_2_2_star {ι : Type*} [DecidableEq ι] (g : ℝ → ℝ) (p d : ι → ℝ)
    (J : Finset ι)
    (hg : ConvexOn ℝ (Set.Ici 0) g) (hgm : MonotoneOn g (Set.Ici 0))
    (hp : ∀ i ∈ J, 0 ≤ p i)
    (l : List ι) (hl : MooreLateJobs.Shared.IsSchedule J l) (hedd : IsEDDOrder d l)
    (hW : ∀ i ∈ J, startTime p l i ≤ d i) :
    IsOptimal g p d J l := by sorry

end EmmonsTardiness.EDD

