import Mathlib
import Definitions.Def_ArrowDebreu_Shared_Economy
import Definitions.Def_ArrowDebreu_ThmI_AssumptionsItoIV
import Definitions.Def_ArrowDebreu_Shared_IsCompetitiveEquilibrium
open ArrowDebreu.Shared

namespace ArrowDebreu.ThmI

/-- **Theorem I (§1.5.1)**, Arrow & Debreu, *Existence of an Equilibrium for a Competitive
Economy*, Econometrica 22 (1954), p. 272 (PDF p. 9): "For any economic system satisfying
Assumptions I–IV, there is a competitive equilibrium."

For every economy with `l ≥ 1` commodities, `m` consumption units and `n` production units that
satisfies Assumptions I.a–I.c, II, III.a–III.c and IV.a–IV.b, there are consumption vectors
`x_i^*`, production plans `y_j^*` and a price vector `p^*` satisfying Conditions 1–4
(Definition 1.5.0).

**Formalization Note.** `0 < l` is added: with `l = 0` the price simplex
`P = {p ≧ 0 | Σ_h p_h = 1}` is empty, and for `m = n = 0` all of Assumptions I–IV hold while no
competitive equilibrium exists. The paper takes `l ≥ 1` for granted. -/
theorem theorem_I {l m n : ℕ} (hl : 0 < l) (E : Economy l m n) (hE : AssumptionsItoIV E) :
    ∃ (x : Fin m → Fin l → ℝ) (y : Fin n → Fin l → ℝ) (p : Fin l → ℝ),
      IsCompetitiveEquilibrium E x y p := by sorry

end ArrowDebreu.ThmI
