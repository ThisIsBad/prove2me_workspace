import Mathlib
import Definitions.Def_KumarSeidman_Supervisor_System
import Definitions.Def_KumarSeidman_Supervisor_Trajectory
import Definitions.Def_KumarSeidman_Supervisor_Mechanism

namespace KumarSeidman.Supervisor

/-- Lemma 1 3) (Kumar–Seidman 1990, p. 296), with the strict threshold needed for re-entry.
If `b = b_{p,i}` enters `Q_m` at `t_in`, `x_{p,i}(σ) ≥ max(γ_m d_p, z_{p,i})` on
`[t_in, t']` and `x_{p,i}(σ) > z_{p,i}` on `(t_in, t']`, then
`t' − t_in ≤ (1 + β_{p,i}(t_in)/(ζ_m d_p τ_{p,i}))(γ_m − ζ_m)`. -/
theorem lemma1_large_duration {P M : ℕ} (S : System P M) (hcap : S.CapacityCondition)
    (γ : Fin M → ℝ) (hγ : GammaCondition S γ) (z : Buffer S → ℝ) (hz : ∀ b, 0 ≤ z b)
    (T : Trajectory S) (hT : T.Supervised γ z) (b : Buffer S) (tIn t' : ℝ)
    (hin : T.EntersQ z b tIn)
    (hge : ∀ σ ∈ Set.Icc tIn t', max (γ (S.mach b) * S.d b.1) (z b) ≤ T.x b σ)
    (hgt : ∀ σ ∈ Set.Ioc tIn t', z b < T.x b σ) :
    t' - tIn ≤
      (1 + backlog T b tIn / (zeta S γ (S.mach b) * S.d b.1 * S.tau b)) *
        (γ (S.mach b) - zeta S γ (S.mach b)) := by sorry

end KumarSeidman.Supervisor

