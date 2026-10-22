import Mathlib
import Definitions.Def_KumarSeidman_CAF_System
import Definitions.Def_KumarSeidman_CAF_Trajectory
import Definitions.Def_KumarSeidman_CAF_Policy
import Definitions.Def_KumarSeidman_CAF_Lyapunov

namespace KumarSeidman.CAF

/-- Boundedness on the minimal classes (p. 295): under (14) and a CAF policy, the levels of
the buffers of every machine `m` whose class is minimal are bounded on `[0, ∞)`. -/
theorem minimal_class_bounded {P M : ℕ} (S : System P M) (h14 : S.StringentCapacityCondition)
    (ε K : Fin M → ℝ) (T : Trajectory S) (hT : T.IsCAF ε K) (m : Fin M)
    (hmin : S.IsMinimal m) :
    ∀ b ∈ S.B m, ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → T.x b t ≤ C := by sorry

end KumarSeidman.CAF

