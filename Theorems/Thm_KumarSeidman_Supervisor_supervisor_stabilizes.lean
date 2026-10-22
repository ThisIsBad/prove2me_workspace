import Mathlib
import Definitions.Def_KumarSeidman_Supervisor_System
import Definitions.Def_KumarSeidman_Supervisor_Trajectory
import Definitions.Def_KumarSeidman_Supervisor_Mechanism

namespace KumarSeidman.Supervisor

/-- Theorem 2 (Kumar–Seidman 1990, p. 297). Under the capacity condition (1), with run-length
parameters `γ` satisfying (24) and arbitrary thresholds `z ≥ 0`, every trajectory of an
arbitrary scheduling policy modified by the supervisor at all machines keeps every buffer level
bounded over `[0, ∞)`, from every initial state. -/
theorem supervisor_stabilizes {P M : ℕ} (S : System P M) (hcap : S.CapacityCondition)
    (γ : Fin M → ℝ) (hγ : GammaCondition S γ) (z : Buffer S → ℝ) (hz : ∀ b, 0 ≤ z b)
    (T : Trajectory S) (hT : T.Supervised γ z) :
    T.IsStable := by sorry

end KumarSeidman.Supervisor

