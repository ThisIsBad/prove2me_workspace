import Mathlib
import Definitions.Def_ArrowDebreu_Shared_Economy
import Definitions.Def_ArrowDebreu_ThmI_AssumptionsItoIV
import Definitions.Def_ArrowDebreu_Shared_IsCompetitiveEquilibrium
import Definitions.Def_ArrowDebreu_Shared_AbstractEconomy
import Definitions.Def_ArrowDebreu_ThmI_economyE
open ArrowDebreu.Shared

namespace ArrowDebreu.ThmI

/-- **§3.4.1**, Arrow & Debreu, Econometrica 22 (1954), p. 279 (PDF p. 16): "It has been shown,
therefore, that the point `(x_1^*, ⋯, x_m^*, y_1^*, ⋯, y_n^*, p^*)` is also an equilibrium point
for E".

For an economy satisfying Assumptions I–IV and a positive real `c` chosen as in §3.3.3 (the cube
`C` contains in its interior all `X̂_i` and all `Ŷ_j`), every equilibrium point of the truncated
abstract economy `Ẽ` of §3.3.4 is an equilibrium point of the abstract economy `E` of §3.1.0.

**Formalization Note.** The second half of the paper's sentence ("as shown in 3.2., it is,
therefore, a competitive equilibrium") is the item `E_equilibrium_is_competitive`. -/
theorem Etilde_equilibrium_is_E_equilibrium {l m n : ℕ} (E : Economy l m n)
    (hE : AssumptionsItoIV E) (c : ℝ) (hc : 0 < c)
    (hX : ∀ i, Xhat E i ⊆ interior (cube l c)) (hY : ∀ j, Yhat E j ⊆ interior (cube l c))
    (a : Player m n → Fin l → ℝ) (ha : (economyEtilde E c).IsEquilibriumPoint a) :
    (economyE E E.X E.Y).IsEquilibriumPoint a := by sorry

end ArrowDebreu.ThmI
