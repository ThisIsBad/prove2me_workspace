import Mathlib
import Definitions.Def_ArrowDebreu_Shared_Economy
import Definitions.Def_ArrowDebreu_ThmI_AssumptionsItoIV
import Definitions.Def_ArrowDebreu_Shared_IsCompetitiveEquilibrium
import Definitions.Def_ArrowDebreu_Shared_AbstractEconomy
import Definitions.Def_ArrowDebreu_ThmI_economyE
open ArrowDebreu.Shared

namespace ArrowDebreu.ThmI

/-- **§3.3.2, display (2)**, Arrow & Debreu, Econometrica 22 (1954), p. 277 (PDF p. 14): "`X̂_i` is
bounded for all `i`", where `X̂_i` (§3.3.0, p. 276) is the set of consumption vectors `x_i ∈ X_i`
that can be completed by `x_{i'} ∈ X_{i'}` (`i' ≠ i`) and `y_j ∈ Y_j` (all `j`) with
`z = Σ_i x_i − Σ_j y_j − ζ ≦ 0`.

**Formalization Note.** §3.3.2 uses Assumption II and display (7) of §3.3.1, which rests on
I.a, I.b, I.c and II; these are the hypotheses. -/
theorem Xhat_bounded {l m n : ℕ} (E : Economy l m n) (hIa : AssumptionIa E) (hIb : AssumptionIb E)
    (hIc : AssumptionIc E) (hII : AssumptionII E) :
    ∀ i, Bornology.IsBounded (Xhat E i) := by sorry

end ArrowDebreu.ThmI
