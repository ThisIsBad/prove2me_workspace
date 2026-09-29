import Mathlib
import Definitions.Def_ArrowDebreu_Shared_Economy
import Definitions.Def_ArrowDebreu_ThmI_AssumptionsItoIV
import Definitions.Def_ArrowDebreu_Shared_IsCompetitiveEquilibrium
import Definitions.Def_ArrowDebreu_Shared_AbstractEconomy
import Definitions.Def_ArrowDebreu_ThmI_economyE
open ArrowDebreu.Shared

namespace ArrowDebreu.ThmI

/-- **§3.2**, Arrow & Debreu, Econometrica 22 (1954), pp. 275–276 (PDF pp. 12–13): "(1) and (2)
together assert Condition 4. It has been shown that any equilibrium point of E satisfies
Conditions 1–4 and hence is a competitive equilibrium."

For an economy satisfying Assumptions I–IV, if `a^*` is an equilibrium point of the abstract
economy `E` of §3.1.0, then its consumption vectors, production plans and price vector
`(x_1^*, ⋯, x_m^*, y_1^*, ⋯, y_n^*, p^*)` form a competitive equilibrium (Definition 1.5.0).

**Formalization Note.** Only the forward direction is stated; the paper's "The converse is
obviously also true" is not part of this item. -/
theorem E_equilibrium_is_competitive {l m n : ℕ} (E : Economy l m n) (hE : AssumptionsItoIV E)
    (a : Player m n → Fin l → ℝ) (ha : (economyE E E.X E.Y).IsEquilibriumPoint a) :
    IsCompetitiveEquilibrium E (consOf a) (prodOf a) (priceOf a) := by sorry

end ArrowDebreu.ThmI
