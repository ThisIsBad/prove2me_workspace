import Mathlib
import Definitions.Def_ArrowDebreu_Shared_Economy
import Definitions.Def_ArrowDebreu_ThmI_AssumptionsItoIV
import Definitions.Def_ArrowDebreu_Shared_IsCompetitiveEquilibrium
import Definitions.Def_ArrowDebreu_Shared_AbstractEconomy
import Definitions.Def_ArrowDebreu_ThmI_economyE
open ArrowDebreu.Shared

namespace ArrowDebreu.ThmI

/-- **§3.3.1, display (7)**, Arrow & Debreu, Econometrica 22 (1954), p. 277 (PDF p. 14): "`Ŷ_j` is
bounded for all `j`", where `Ŷ_j` (§3.3.0, p. 276) is the set of production plans `y_j ∈ Y_j`
that can be completed by `x_i ∈ X_i` (all `i`) and `y_{j'} ∈ Y_{j'}` (`j' ≠ j`) with
`z = Σ_i x_i − Σ_j y_j − ζ ≦ 0`.

**Formalization Note.** The argument of §3.3.1 uses Assumptions I.a, I.b, I.c and II; these are
the hypotheses. Boundedness is Mathlib's `Bornology.IsBounded` in `R^l` (sup-norm, equivalent to
the Euclidean one). -/
theorem Yhat_bounded {l m n : ℕ} (E : Economy l m n) (hIa : AssumptionIa E) (hIb : AssumptionIb E)
    (hIc : AssumptionIc E) (hII : AssumptionII E) :
    ∀ j, Bornology.IsBounded (Yhat E j) := by sorry

end ArrowDebreu.ThmI
