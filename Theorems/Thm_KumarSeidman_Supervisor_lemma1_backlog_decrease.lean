import Mathlib
import Definitions.Def_KumarSeidman_Supervisor_System
import Definitions.Def_KumarSeidman_Supervisor_Trajectory
import Definitions.Def_KumarSeidman_Supervisor_Mechanism

namespace KumarSeidman.Supervisor

/-- Lemma 1 2) (Kumar–Seidman 1990, p. 296). If buffer `b = b_{p,i}` enters `Q_m` at
`t_in` with `x_{p,i}(t_in) ≥ γ_m d_p`, then at the completion `t_complete` of its subsequent
processing run the backlog has dropped by at least `ζ_m d_p τ_{p,i}`. -/
theorem lemma1_backlog_decrease {P M : ℕ} (S : System P M) (hcap : S.CapacityCondition)
    (γ : Fin M → ℝ) (hγ : GammaCondition S γ) (z : Buffer S → ℝ) (hz : ∀ b, 0 ≤ z b)
    (T : Trajectory S) (hT : T.Supervised γ z) (b : Buffer S) (tIn : ℝ)
    (hin : T.EntersQ z b tIn) (k : ℕ) (hk : T.IsNextRun b tIn k)
    (hnext : T.HasNext (S.mach b) k)
    (hlevel : γ (S.mach b) * S.d b.1 ≤ T.x b tIn) :
    backlog T b (T.s (S.mach b) (k + 1)) ≤
      backlog T b tIn - zeta S γ (S.mach b) * S.d b.1 * S.tau b := by sorry

end KumarSeidman.Supervisor

