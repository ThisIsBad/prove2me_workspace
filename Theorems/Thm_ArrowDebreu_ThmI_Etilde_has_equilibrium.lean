import Mathlib
import Definitions.Def_ArrowDebreu_Shared_Economy
import Definitions.Def_ArrowDebreu_ThmI_AssumptionsItoIV
import Definitions.Def_ArrowDebreu_Shared_IsCompetitiveEquilibrium
import Definitions.Def_ArrowDebreu_Shared_AbstractEconomy
import Definitions.Def_ArrowDebreu_ThmI_economyE
open ArrowDebreu.Shared

namespace ArrowDebreu.ThmI

/-- **§3.4.0**, Arrow & Debreu, Econometrica 22 (1954), p. 279 (PDF p. 16): "The existence of an
equilibrium point `(x_1^*, ⋯, x_m^*, y_1^*, ⋯, y_n^*, p^*)` for the abstract economy `Ẽ` has,
therefore, been demonstrated."

For an economy with `l ≥ 1` commodities satisfying Assumptions I–IV, and a positive real `c`
chosen as in §3.3.3 (the cube `C = {x | |x_h| ≦ c for all h}` contains in its interior all `X̂_i`
and all `Ŷ_j`), the truncated abstract economy `Ẽ` of §3.3.4 has an equilibrium point.

**Formalization Note.** `0 < l` is needed: for `l = 0` the price simplex `P` is empty and no
abstract economy containing the market participant has an equilibrium point. "Interior" is the
topological interior in `R^l`. -/
theorem Etilde_has_equilibrium {l m n : ℕ} (hl : 0 < l) (E : Economy l m n)
    (hE : AssumptionsItoIV E) (c : ℝ) (hc : 0 < c)
    (hX : ∀ i, Xhat E i ⊆ interior (cube l c)) (hY : ∀ j, Yhat E j ⊆ interior (cube l c)) :
    ∃ a, (economyEtilde E c).IsEquilibriumPoint a := by sorry

end ArrowDebreu.ThmI
