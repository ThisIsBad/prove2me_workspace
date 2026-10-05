import Mathlib
import Definitions.Def_EmmonsTardiness_EDD_Model

namespace EmmonsTardiness.EDD

/-- Emmons 1969, p. 713, Corollary 2.1*: if `d_j = max_i {d_i}` and `d_j + p_j ≥ p = Σ_J p_i`,
then `J_j` is last in some schedule minimizing `Σ_J g(T_i)`. -/
theorem corollary_2_1_star {ι : Type*} [DecidableEq ι] (g : ℝ → ℝ) (p d : ι → ℝ)
    (J : Finset ι)
    (hg : ConvexOn ℝ (Set.Ici 0) g) (hgm : MonotoneOn g (Set.Ici 0))
    (hp : ∀ i ∈ J, 0 ≤ p i)
    (j : ι) (hj : j ∈ J) (hmax : ∀ i ∈ J, d i ≤ d j)
    (hlast : ∑ i ∈ J, p i ≤ d j + p j) :
    ∃ l : List ι, IsOptimal g p d J l ∧ l.getLast? = some j := by sorry

end EmmonsTardiness.EDD

