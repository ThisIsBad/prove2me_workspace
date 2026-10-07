import Mathlib
import Definitions.Def_SchedComplexity_PrecChain_Model

namespace SchedComplexity.PrecChain

/-- Brucker, Lenstra & Rinnooy Kan (1975), proof of Theorem 1(l), p. 9: "Any instance of `P'`
has a solution with value `C_max ≤ n'p_*`." Every instance of
`n'|m|I,prec,1≤p_j1≤p_*|C_max` (at least one machine, processing times in `[1, p_*]`, acyclic
precedence) has a feasible schedule in which every job completes by `n' p_*`. -/
theorem cmax_le_n_pstar (pstar : ℕ) (I : Instance) (hI : I.InClass pstar) :
    CmaxYes I (I.n * pstar) := by sorry

end SchedComplexity.PrecChain

