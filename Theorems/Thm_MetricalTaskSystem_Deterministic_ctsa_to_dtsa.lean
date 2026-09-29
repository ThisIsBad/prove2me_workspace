import Mathlib
import Definitions.Def_MetricalTaskSystem_Deterministic_Model
import Definitions.Def_MetricalTaskSystem_Deterministic_ContinuousTime

namespace MetricalTaskSystem.Deterministic

/-- **Lemma 3.1** (Borodin–Linial–Saks 1992, p. 752). For any on-line continuous-time
scheduling algorithm `A'` there is an on-line discrete-time scheduling algorithm `A` that
performs at least as well as `A'` on every (nonnegative) task sequence, from every initial
state. -/
theorem ctsa_to_dtsa {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (d : S → S → ℝ) (hd : IsTaskSystem d) (A' : CTSA S) (hA' : IsCTSA A') :
    ∃ A : OnlineAlgorithm S, ∀ (s₀ : S) (m : ℕ) (T : Fin m → S → ℝ), (∀ i s, 0 ≤ T i s) →
      onlineCost d A s₀ T ≤ ctsaCost d A' s₀ T := by sorry

end MetricalTaskSystem.Deterministic

