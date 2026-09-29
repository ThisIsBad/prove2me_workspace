import Mathlib
import Definitions.Def_ArrowDebreu_Shared_Economy
import Definitions.Def_ArrowDebreu_ThmI_AssumptionsItoIV
import Definitions.Def_ArrowDebreu_Shared_IsCompetitiveEquilibrium
import Definitions.Def_ArrowDebreu_Shared_AbstractEconomy
import Definitions.Def_ArrowDebreu_ThmI_economyE
open ArrowDebreu.Shared

namespace ArrowDebreu.ThmI

/-- **§3.1.2, display (2)**, Arrow & Debreu, Econometrica 22 (1954), p. 275 (PDF p. 12):
"Condition 2 is satisfied at an equilibrium point of the abstract economy E."

Here `E = economyE E E.X E.Y` is the abstract economy of §3.1.0, whose consumers face the
budget `p·x_i ≦ p·ζ_i + max[0, Σ_j α_{ij} p·y_j]`; the claim is that at an equilibrium point
`a^*` the consumption vectors `x_i^*` satisfy Condition 2 at the prices `p^*` and production
plans `y_j^*` of `a^*`.

**Formalization Note.** The paragraph uses Assumption I.a (`0 ∈ Y_j`) and Assumption IV.b
(`α_{ij} ≧ 0`); these are the hypotheses. -/
theorem condition2_at_E_equilibrium {l m n : ℕ} (E : Economy l m n) (hIa : AssumptionIa E)
    (hIVb : AssumptionIVb E) (a : Player m n → Fin l → ℝ)
    (ha : (economyE E E.X E.Y).IsEquilibriumPoint a) :
    Condition2 E (priceOf a) (consOf a) (prodOf a) := by sorry

end ArrowDebreu.ThmI
