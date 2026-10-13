import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_ReflectedBSDE_StoppingControl_Setting

namespace ReflectedBSDE.StoppingControl

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- A control: a pair of processes `(β_t, γ_t)` valued in `ℝ × ℝ^d`. -/
abbrev Control (Ω : Type*) (d : ℕ) : Type _ :=
  (ℝ≥0 → Ω → ℝ) × (ℝ≥0 → Ω → Fin d → ℝ)

/-- §7, p. 724: the conjugate function
`F(ω, t, β, γ) = sup_{(y, z) ∈ ℝ × ℝ^d} [f(ω, t, y, z) − βy − ⟨γ, z⟩]`, valued in `(−∞, +∞]`
(computed in `EReal`, so an unbounded supremum is `+∞`). -/
noncomputable def conj {d : ℕ} (f : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ) (ω : Ω) (t : ℝ≥0)
    (β : ℝ) (γ : Fin d → ℝ) : EReal :=
  ⨆ (y : ℝ) (z : Fin d → ℝ), ((f t ω y z - β * y - dot γ z : ℝ) : EReal)

/-- §7, p. 724: `D^F_t(ω) = {(β, γ) ∈ ℝ × ℝ^d : F(ω, t, β, γ) < ∞}`. -/
def conjDomain {d : ℕ} (f : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ) (ω : Ω) (t : ℝ≥0) :
    Set (ℝ × (Fin d → ℝ)) :=
  {p | conj f ω t p.1 p.2 < ⊤}

/-- §7, p. 725: the class `𝒜` of bounded progressively measurable `ℝ × ℝ^d`-valued processes
`(β_t, γ_t)` with `E ∫₀ᵀ F(t, β_t, γ_t)² dt < ∞`. Boundedness: one constant `C` with
`|β_t(ω)| + |γ_t(ω)| ≤ C` for all `t ∈ [0, T]` and all `ω`. The square of the extended real
`F` is taken in `ℝ≥0∞` with `|+∞|² = +∞`, so the finiteness of the integral forces
`F(t, β_t, γ_t) < ∞` for `dt × dP`-a.e. `(t, ω)`. -/
def admissible {d : ℕ} (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (T : ℝ≥0)
    (f : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ) : Set (Control Ω d) :=
  {c | IsStronglyProgressive 𝓕 c.1 ∧ IsStronglyProgressive 𝓕 c.2 ∧
    (∃ C : ℝ, ∀ t ≤ T, ∀ ω, |c.1 t ω| + eucNorm (c.2 t ω) ≤ C) ∧
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      EReal.abs (conj f ω s.toNNReal (c.1 s.toNNReal ω) (c.2 s.toNNReal ω)) ^ 2 ∂volume ∂P < ⊤}

/-- §7, p. 725: the affine coefficient
`f^{β,γ}(t, y, z) = F(t, β_t, γ_t) + β_t y + ⟨γ_t, z⟩` (with `F` read as a real number; on the
`dt × dP`-null set where `F(t, β_t, γ_t) = +∞` for `(β, γ) ∈ 𝒜` the value used is `0`). -/
noncomputable def affineCoeff {d : ℕ} (f : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ) (c : Control Ω d) :
    ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ :=
  fun t ω y z => (conj f ω t (c.1 t ω) (c.2 t ω)).toReal + c.1 t ω * y + dot (c.2 t ω) z

/-- `J = (J₁, …, J_d)` are Itô integrals `Jⱼ = ∫₀^· γʲ_s dBʲ_s` on `[0, T]` (in the sense of
`Peng1990.SMP.IsItoIntegral`) whose paths are continuous on `[0, T]` for every `ω`
(a continuous version). -/
def IsContItoIntegral {d : ℕ} (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (T : ℝ≥0)
    (B : ℝ≥0 → Ω → Fin d → ℝ) (γ : ℝ≥0 → Ω → Fin d → ℝ) (J : Fin d → ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ j, Peng1990.SMP.IsItoIntegral 𝓕 P T (fun s ω => B s ω j) (fun s ω => γ s ω j) (J j) ∧
    ∀ ω, ContinuousOn (fun s => J j s ω) (Set.Iic T)

/-- The solution `Γ_{t,s}`, `t ≤ s ≤ T`, of the linear SDE
`dΓ_{t,s} = Γ_{t,s}(β_s ds + (γ_s, dB_s))`, `Γ_{t,t} = 1`, in closed (Doléans-Dade) form
`Γ_{t,s} = exp(∫ₜˢ β_r dr + Σⱼ (Jⱼ(s) − Jⱼ(t)) − ½ ∫ₜˢ |γ_r|² dr)`, where `Jⱼ = ∫₀^· γʲ dBʲ`.
`Γ_{0,s}` is the process `Γ_s` of Proposition 7.1. -/
noncomputable def linGamma {d : ℕ} (β : ℝ≥0 → Ω → ℝ) (γ : ℝ≥0 → Ω → Fin d → ℝ)
    (J : Fin d → ℝ≥0 → Ω → ℝ) (t s : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp ((∫ r in Set.Icc (t : ℝ) s, β r.toNNReal ω) + ∑ j, (J j s ω - J j t ω)
    - (1 / 2) * ∫ r in Set.Icc (t : ℝ) s, ∑ j, γ r.toNNReal ω j ^ 2)

/-- Proposition 7.1, p. 724: the payoff
`Γ_v ξ 1_{v=T} + Γ_v S_v 1_{v<T} + ∫ₜᵛ Γ_s δ_s ds` of the stopping time `v`, with `Γ_s = Γ_{0,s}`. -/
noncomputable def affinePayoff {d : ℕ} (T : ℝ≥0) (ξ : Ω → ℝ) (S δ β : ℝ≥0 → Ω → ℝ)
    (γ : ℝ≥0 → Ω → Fin d → ℝ) (J : Fin d → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (v : Ω → ℝ≥0) (ω : Ω) : ℝ :=
  linGamma β γ J 0 (v ω) ω * ξ ω * (if v ω = T then 1 else 0)
    + linGamma β γ J 0 (v ω) ω * S (v ω) ω * (if v ω < T then 1 else 0)
    + ∫ s in Set.Icc (t : ℝ) (v ω), linGamma β γ J 0 s.toNNReal ω * δ s.toNNReal ω

/-- Theorem 7.2, p. 725: the payoff
`Φ(t, v, β, γ) = Γ^{β,γ}_{t,v}[S_v 1_{v<T} + ξ 1_{v=T}] + ∫ₜᵛ Γ^{β,γ}_{t,s} F(s, β_s, γ_s) ds`,
where `J` are the Itô integrals of `γ` defining `Γ^{β,γ}` (`F` read as a real number). -/
noncomputable def payoff {d : ℕ} (T : ℝ≥0) (ξ : Ω → ℝ) (f : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ)
    (S : ℝ≥0 → Ω → ℝ) (c : Control Ω d) (J : Fin d → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (v : Ω → ℝ≥0)
    (ω : Ω) : ℝ :=
  linGamma c.1 c.2 J t (v ω) ω
      * (S (v ω) ω * (if v ω < T then 1 else 0) + ξ ω * (if v ω = T then 1 else 0))
    + ∫ s in Set.Icc (t : ℝ) (v ω),
        linGamma c.1 c.2 J t s.toNNReal ω
          * (conj f ω s.toNNReal (c.1 s.toNNReal ω) (c.2 s.toNNReal ω)).toReal

end ReflectedBSDE.StoppingControl
