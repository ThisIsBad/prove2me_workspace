import Mathlib
import Definitions.Def_SchedComplexity_PrecChain_Model
import Definitions.Def_SchedComplexity_PrecChain_Construction

namespace SchedComplexity.PrecChain

/-- Brucker, Lenstra & Rinnooy Kan (1975), proof of Theorem 1(l), p. 9, first line of the
display: `C_max ≤ y' ⇒ Σ_{j=1}^{j=n} C_j ≤ n'y' + Σ (y' + k) = y`. For an instance `I` of
`P' = n'|m|I,prec,1≤p_j1≤p_*|C_max` and `0 ≤ y' ≤ n' p_*`: if `I` has a feasible schedule with
`C_max ≤ y'`, the constructed instance `chainExtend I y'` has a feasible schedule with
`Σ_j C_j ≤ y = n y' + ½ n''(n'' + 1)`. (The printed sum runs over `k = n'+1, …, n`; the bound
needs `k = 1, …, n''`, the indices of the added jobs. The statement gives the end-to-end bound
`Σ_j C_j ≤ y`.) -/
theorem cmax_le_imp_sumC_le (pstar : ℕ) (I : Instance) (hI : I.InClass pstar) (y' : ℕ)
    (hy' : y' ≤ I.n * pstar) (h : CmaxYes I y') :
    ∃ σ : Schedule (chainExtend I y'), σ.IsFeasible ∧
      (σ.totalCompletion : ℚ) ≤ chainThresholdQ I.n y' := by sorry

end SchedComplexity.PrecChain

