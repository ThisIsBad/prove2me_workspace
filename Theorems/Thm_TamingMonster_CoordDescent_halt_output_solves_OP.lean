import Mathlib
import Definitions.Def_TamingMonster_CoordDescent_Setting
import Definitions.Def_TamingMonster_CoordDescent_Algorithm

namespace TamingMonster.CoordDescent

/-- Lemma 5 (p. 10; proof App. D.1): if Algorithm 2 halts and outputs a weight vector `Q` —
i.e. the loop is entered with nonnegative weights `Q₀`, Steps 4–6 produce `Q = rescale Q₀`, and
no policy has `D_π(Q) > 0` (Step 7 fails and Step 10 halts) — then `Q` satisfies Eq. (3) and
Eq. (2), is nonnegative, and its weights sum to at most 1; that is, `Q` solves (OP). -/
theorem halt_output_solves_OP {X : Type*} {K t : ℕ} (hK : 0 < K) (ht : 0 < t)
    (Pi : Finset (X → Fin K)) (hPi : Pi.Nonempty) (H : History X K t)
    (μ : ℝ) (hμ : 0 < μ) (hμK : μ ≤ 1 / (2 * (K : ℝ)))
    (Q₀ : Pi → ℝ) (hQ₀ : ∀ π, 0 ≤ Q₀ π)
    (hhalt : HaltsAt Pi H μ Q₀) :
    SolvesOP Pi H μ (rescale Pi H μ Q₀) := by sorry

end TamingMonster.CoordDescent

