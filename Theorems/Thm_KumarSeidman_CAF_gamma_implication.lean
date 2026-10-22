import Mathlib
import Definitions.Def_KumarSeidman_CAF_System
import Definitions.Def_KumarSeidman_CAF_Trajectory
import Definitions.Def_KumarSeidman_CAF_Policy
import Definitions.Def_KumarSeidman_CAF_Lyapunov

namespace KumarSeidman.CAF

/-- The `Γ_m` implication (p. 295, after (22)): under (14) and a CAF policy with constants
`ε, K`, for a machine `m` whose class is minimal and two consecutive set-up commencements
`T_n = s_k`, `T_{n+1} = s_{k+1}` (`k ≥ 1`) at `m`,
`V_m(T_n) ≥ Γ_m ⇒ V_m(T_{n+1}) ≤ V_m(T_n) − δ̄`, where
`Γ_m = max (2 δ̄ τ̄ / (ε_m τ̲ (1 − ρ'_m)) + K_m τ̄ / ε_m, δ̄)`. -/
theorem gamma_implication {P M : ℕ} (S : System P M) (h14 : S.StringentCapacityCondition)
    (ε K : Fin M → ℝ) (T : Trajectory S) (hT : T.IsCAF ε K) (m : Fin M)
    (hmin : S.IsMinimal m) (hB : (S.B m).Nonempty) (k : ℕ) (hk : 1 ≤ k)
    (hnext : T.HasNext m k) (hV : S.Gamma m hB ε K ≤ T.V m (T.s m k)) :
    T.V m (T.s m (k + 1)) ≤ T.V m (T.s m k) - S.deltaBar m := by sorry

end KumarSeidman.CAF

