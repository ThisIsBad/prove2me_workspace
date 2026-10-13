import Mathlib
import Definitions.Def_SingleMachinePrec_IntervalReduction_Instance

namespace SingleMachinePrec.IntervalReduction

open Classical in
/-- §7, p. 664: with `k = n² + 1`, the incomparable pairs outside `D` have total weight
`∑_{(i,j) ∈ inc(I) \ D} p_i w_j < 1`, and therefore the minimum vertex cover of the unweighted
graph `G′_I` has size `⌊w(C_I)⌋`. -/
theorem light_weight {N : ℕ} {G : SimpleGraph (Fin N)} (L : TreeLayout G) :
    (∑ u : IncPair (prec L),
        if InD L u.1.1 u.1.2 then 0
        else vertexWeight (prec L) (procTime L (kVal L)) (weight L (kVal L)) u) < 1 ∧
    (GIprime L).vertexCoverNum = ((⌊tauW L⌋₊ : ℕ) : ℕ∞) := by sorry

end SingleMachinePrec.IntervalReduction

