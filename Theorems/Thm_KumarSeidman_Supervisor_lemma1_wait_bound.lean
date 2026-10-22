import Mathlib
import Definitions.Def_KumarSeidman_Supervisor_System
import Definitions.Def_KumarSeidman_Supervisor_Trajectory
import Definitions.Def_KumarSeidman_Supervisor_Mechanism

namespace KumarSeidman.Supervisor

/-- Lemma 1 1) (Kumar–Seidman 1990, p. 296, (25)–(26)). If buffer `b` enters the priority
queue `Q_m` (`m = μ_b`) at time `t_in`, then its subsequent processing run exists and is
completed by `t_in + γ_m − ζ_m`. -/
theorem lemma1_wait_bound {P M : ℕ} (S : System P M) (hcap : S.CapacityCondition)
    (γ : Fin M → ℝ) (hγ : GammaCondition S γ) (z : Buffer S → ℝ) (hz : ∀ b, 0 ≤ z b)
    (T : Trajectory S) (hT : T.Supervised γ z) (b : Buffer S) (tIn : ℝ)
    (hin : T.EntersQ z b tIn) :
    ∃ k : ℕ, T.IsNextRun b tIn k ∧ T.HasNext (S.mach b) k ∧
      T.s (S.mach b) (k + 1) - tIn ≤ γ (S.mach b) - zeta S γ (S.mach b) := by sorry

end KumarSeidman.Supervisor

