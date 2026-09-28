import Mathlib
import Definitions.Def_TamingMonster_CoordDescent_Setting
import Definitions.Def_TamingMonster_CoordDescent_Algorithm

namespace TamingMonster.CoordDescent

/-- Theorem 3 (p. 6): Algorithm 2 with `Q_init := 0` halts in at most `4 ln(1/(Kμ))/μ`
iterations and outputs a solution `Q` to (OP).
(i) Every run from `Q_init = 0`, whatever policy each Step 8 picks among those with
`D_π > 0`, executes Step 8 at most `4 ln(1/(Kμ))/μ` times; since a state that does not halt
always admits a further Step 8, every run halts within that many updates.
(ii) When a run halts, its output `rescale Q⁽ⁿ⁾` solves (OP). -/
theorem coordinateDescent_halts_solves_OP {X : Type*} {K t : ℕ} (hK : 0 < K) (ht : 0 < t)
    (Pi : Finset (X → Fin K)) (hPi : Pi.Nonempty) (H : History X K t)
    (μ : ℝ) (hμ : 0 < μ) (hμK : μ ≤ 1 / (2 * (K : ℝ))) :
    (∀ (n : ℕ) (Qs : ℕ → Pi → ℝ), IsRun Pi H μ (fun _ => 0) n Qs →
        (n : ℝ) ≤ 4 * Real.log (1 / ((K : ℝ) * μ)) / μ) ∧
    (∀ (n : ℕ) (Qs : ℕ → Pi → ℝ), IsRun Pi H μ (fun _ => 0) n Qs →
        HaltsAt Pi H μ (Qs n) → SolvesOP Pi H μ (rescale Pi H μ (Qs n))) := by sorry

end TamingMonster.CoordDescent

