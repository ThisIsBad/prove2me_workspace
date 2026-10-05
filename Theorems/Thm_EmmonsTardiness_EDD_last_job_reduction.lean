import Mathlib
import Definitions.Def_EmmonsTardiness_EDD_Model

namespace EmmonsTardiness.EDD

/-- Emmons 1969, p. 706, proof of Corollary 2.2, last sentence ("Remove it from the problem,
redefine p, and repeat"): if some optimal schedule of `J` ends with `J_j`, then appending `J_j`
to any optimal schedule of the remaining jobs `J \ {J_j}` gives an optimal schedule of `J`. -/
theorem last_job_reduction {ι : Type*} [DecidableEq ι] (g : ℝ → ℝ) (p d : ι → ℝ)
    (J : Finset ι) (j : ι) (hj : j ∈ J)
    (hlast : ∃ l : List ι, IsOptimal g p d J l ∧ l.getLast? = some j)
    (l' : List ι) (hl' : IsOptimal g p d (J.erase j) l') :
    IsOptimal g p d J (l' ++ [j]) := by sorry

end EmmonsTardiness.EDD

