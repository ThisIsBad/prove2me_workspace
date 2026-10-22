import Mathlib
import Definitions.Def_KumarSeidman_Supervisor_System
import Definitions.Def_KumarSeidman_Supervisor_Trajectory
import Definitions.Def_KumarSeidman_Supervisor_Mechanism

namespace KumarSeidman.Supervisor

/-- Lemma 1 4) (Kumar–Seidman 1990, p. 296, right column). If `x_{p,i}(σ) ≥ g_{p,i}` throughout `[t, t']`,
where `g_{p,i} = max(γ_m d_p, z_{p,i}) + γ_m d_p`, then `t' − t ≤ a_{p,i} + c_{p,i} β_{p,i}(t)`
with `a_{p,i} = (2 + (γ_m − ζ_m)/ζ_m)(γ_m − ζ_m)` and
`c_{p,i} = (γ_m − ζ_m)/(ζ_m d_p τ_{p,i})`. -/
theorem lemma1_interval_bound {P M : ℕ} (S : System P M) (hcap : S.CapacityCondition)
    (γ : Fin M → ℝ) (hγ : GammaCondition S γ) (z : Buffer S → ℝ) (hz : ∀ b, 0 ≤ z b)
    (T : Trajectory S) (hT : T.Supervised γ z) (b : Buffer S) (t t' : ℝ) (ht : 0 ≤ t)
    (hx : ∀ σ ∈ Set.Icc t t',
      max (γ (S.mach b) * S.d b.1) (z b) + γ (S.mach b) * S.d b.1 ≤ T.x b σ) :
    t' - t ≤
      (2 + (γ (S.mach b) - zeta S γ (S.mach b)) / zeta S γ (S.mach b)) *
          (γ (S.mach b) - zeta S γ (S.mach b)) +
        (γ (S.mach b) - zeta S γ (S.mach b)) /
            (zeta S γ (S.mach b) * S.d b.1 * S.tau b) * backlog T b t := by sorry

end KumarSeidman.Supervisor

