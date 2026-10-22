import Mathlib
import Definitions.Def_KumarSeidman_CAF_System
import Definitions.Def_KumarSeidman_CAF_Trajectory
import Definitions.Def_KumarSeidman_CAF_Policy
import Definitions.Def_KumarSeidman_CAF_Lyapunov

namespace KumarSeidman.CAF

/-- The recurrence of the induction step of the proof of Theorem 1 (p. 295, generalizing
(17)). Let `U` be an upstream-closed set of machines whose buffers have total content at most
`Γ` at all times `t ≥ 0`, and let `m ∉ U` be a machine whose class is minimal among the
machines outside `U`. Under (14) and a clearing policy, for two consecutive set-up
commencements `T_n = s_k`, `T_{n+1} = s_{k+1}` (`k ≥ 1`) at `m`,
`V_m(T_{n+1}) ≤ max {Γ̄, V_m(T_n) − (1 − ρ'_m)(T_{n+1} − T_n) + δ̄ + Γ̄}`,
with `Γ̄ = Σ_{(p,i): μ_{p,i} = m, μ_{p,i−1} ≠ m} Γ [τ_{p,i} + ⋯ + τ_{p,i+η_{p,i}−1}]`. -/
theorem induction_recurrence {P M : ℕ} (S : System P M) (h14 : S.StringentCapacityCondition)
    (T : Trajectory S) (hT : T.IsClearing) (U : Finset (Fin M)) (hU : S.UpstreamClosed U)
    (Γ : ℝ) (hΓ : ∀ t : ℝ, 0 ≤ t →
      ∑ b ∈ Finset.univ.filter (fun b : Buffer S => S.mach b ∈ U), T.x b t ≤ Γ)
    (m : Fin M) (hmU : m ∉ U) (hmin : ∀ m' : Fin M, m' ∉ U → S.Reach m' m → S.Reach m m')
    (k : ℕ) (hk : 1 ≤ k) (hnext : T.HasNext m k) :
    T.V m (T.s m (k + 1)) ≤
      max (S.GammaBar m Γ) (T.V m (T.s m k) - (1 - S.rhoPrime m) * (T.s m (k + 1) - T.s m k)
        + S.deltaBar m + S.GammaBar m Γ) := by sorry

end KumarSeidman.CAF

