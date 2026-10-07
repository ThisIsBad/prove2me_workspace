import Mathlib
import Definitions.Def_SchedComplexity_PrecChain_Model
import Definitions.Def_SchedComplexity_PrecChain_Construction

namespace SchedComplexity.PrecChain

/-- Brucker, Lenstra & Rinnooy Kan (1975), proof of Theorem 1(l), p. 9, second line of the
display: `C_max > y' ⇒ Σ_{j=1}^{j=n} C_j > y' + Σ (y' + 1 + k) = y`. For an instance `I` of
`P' = n'|m|I,prec,1≤p_j1≤p_*|C_max` and `0 ≤ y' ≤ n' p_*`: if every feasible schedule of `I`
has `C_max > y'` (no feasible schedule has `C_j ≤ y'` for all `j`), then every feasible
schedule of the constructed instance `chainExtend I y'` has `Σ_j C_j > y = n y' + ½ n''(n'' + 1)`.
(The printed sum runs over `k = n'+1, …, n`; the bound needs `k = 1, …, n''`. The statement
gives the end-to-end bound `Σ_j C_j > y`.) -/
theorem cmax_gt_imp_sumC_gt (pstar : ℕ) (I : Instance) (hI : I.InClass pstar) (y' : ℕ)
    (hy' : y' ≤ I.n * pstar) (h : ¬ CmaxYes I y') :
    ∀ σ : Schedule (chainExtend I y'), σ.IsFeasible →
      chainThresholdQ I.n y' < (σ.totalCompletion : ℚ) := by sorry

end SchedComplexity.PrecChain

