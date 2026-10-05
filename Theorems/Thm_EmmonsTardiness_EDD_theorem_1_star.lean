import Mathlib
import Definitions.Def_EmmonsTardiness_EDD_Model

namespace EmmonsTardiness.EDD

/-- Emmons 1969, p. 713, Theorem 1*: for any two jobs `J_j`, `J_k` with `j < k`, if `d_j ≤ d_k`
then `j ← k`: some schedule minimizing `Σ_J g(T_i)` has `J_j` before `J_k`. -/
theorem theorem_1_star {ι : Type*} [LinearOrder ι] (g : ℝ → ℝ) (p d : ι → ℝ) (J : Finset ι)
    (hg : ConvexOn ℝ (Set.Ici 0) g) (hgm : MonotoneOn g (Set.Ici 0))
    (hp : ∀ i ∈ J, 0 ≤ p i) (hidx : EmmonsTardiness.SPT.IsSPTIndexed p d J)
    (j k : ι) (hj : j ∈ J) (hk : k ∈ J) (hjk : j < k) (hd : d j ≤ d k) :
    ∃ l : List ι, IsOptimal g p d J l ∧ EmmonsTardiness.SPT.Precedes l j k := by sorry

end EmmonsTardiness.EDD

