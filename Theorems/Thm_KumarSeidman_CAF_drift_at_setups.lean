import Mathlib
import Definitions.Def_KumarSeidman_CAF_System
import Definitions.Def_KumarSeidman_CAF_Trajectory
import Definitions.Def_KumarSeidman_CAF_Policy
import Definitions.Def_KumarSeidman_CAF_Lyapunov

namespace KumarSeidman.CAF

/-- (18) (p. 295): under (14) and a clearing policy, for a machine `m` whose class is minimal
and two consecutive set-up commencements `T_n = s_k`, `T_{n+1} = s_{k+1}` (`k ≥ 1`) at `m`,
`V_m(T_{n+1}) ≤ max [0, V_m(T_n) − (1 − ρ'_m)(T_{n+1} − T_n) + δ̄]`. -/
theorem drift_at_setups {P M : ℕ} (S : System P M) (h14 : S.StringentCapacityCondition)
    (T : Trajectory S) (hT : T.IsClearing) (m : Fin M) (hmin : S.IsMinimal m) (k : ℕ)
    (hk : 1 ≤ k) (hnext : T.HasNext m k) :
    T.V m (T.s m (k + 1)) ≤
      max 0 (T.V m (T.s m k) - (1 - S.rhoPrime m) * (T.s m (k + 1) - T.s m k)
        + S.deltaBar m) := by sorry

end KumarSeidman.CAF

