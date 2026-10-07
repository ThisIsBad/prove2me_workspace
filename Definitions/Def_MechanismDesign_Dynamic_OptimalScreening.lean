import Mathlib
import Definitions.Def_MechanismDesign_Dynamic_Model

/-!
# Virtual valuation, regularity and the optimal sequential screening mechanism
(Krähmer & Strausz, Ch. 11 in Börgers, §11.2.1, pp.214–218)
-/

namespace MechanismDesign.Dynamic

open MeasureTheory

variable {τlo τhi θlo θhi : ℝ}

/-- The **virtual valuation** (p.217):
`ψ(τ, θ) = θ + (1 − G(τ))/g(τ) · (∂F(θ|τ)/∂τ) / f(θ|τ)`. -/
noncomputable def SeqEnv.ψ (E : SeqEnv τlo τhi θlo θhi) (τ θ : ℝ) : ℝ :=
  θ + (1 - E.G τ) / E.g τ * (E.dFdτ θ τ / E.f θ τ)

/-- **Assumption 11.1** (p.217): `ψ(τ, θ)` is increasing (weakly) in `τ` and in `θ` on
`[τ̲, τ̄] × [θ̲, θ̄]`. -/
def SeqEnv.Assumption11_1 (E : SeqEnv τlo τhi θlo θhi) : Prop :=
  (∀ θ ∈ Set.Icc θlo θhi, MonotoneOn (fun τ => E.ψ τ θ) (Set.Icc τlo τhi)) ∧
  (∀ τ ∈ Set.Icc τlo τhi, MonotoneOn (fun θ => E.ψ τ θ) (Set.Icc θlo θhi))

/-- The **exercise price** (p.217): `p(τ) = min {θ̂ ∈ [θ̲, θ̄] | ψ(τ, θ̂) ≥ 0}`. (The page writes
`ψ(θ̂, τ)`, with the arguments swapped.) Written as an infimum, which equals the minimum
whenever the minimum exists; the set is nonempty because `ψ(τ, θ̄) = θ̄ > 0`. -/
noncomputable def SeqEnv.p (E : SeqEnv τlo τhi θlo θhi) (τ : ℝ) : ℝ :=
  sInf {θ | θ ∈ Set.Icc θlo θhi ∧ 0 ≤ E.ψ τ θ}

/-- The constant `t₀(τ)` of **Proposition 11.5** (p.214), for an allocation rule `q` and a
value `tlo` of the payment `t(τ̲, θ̲)` of the lowest type:
`t₀(τ) = t(τ̲, θ̲) − θ̲ q(τ̲, θ̲) + ∫_{τ̲}^{τ} ∫_{θ̲}^{θ̄} q(τ̂, θ̂) ∂F(θ̂|τ̂)/∂τ dθ̂ dτ̂`
`        + ∫_{θ̲}^{θ̄} ∫_{θ̲}^{θ̂} [q(τ, x) f(θ̂|τ) − q(τ̲, x) f(θ̂|τ̲)] dx dθ̂`. -/
noncomputable def SeqEnv.t0 (E : SeqEnv τlo τhi θlo θhi) (q : ℝ → ℝ → ℝ) (tlo τ : ℝ) : ℝ :=
  tlo - θlo * q τlo θlo +
    (∫ τ' in τlo..τ, ∫ θ' in θlo..θhi, q τ' θ' * E.dFdτ θ' τ') +
    ∫ θ' in θlo..θhi, ∫ x in θlo..θ', (q τ x * E.f θ' τ - q τlo x * E.f θ' τlo)

/-- The optimal allocation rule (11.10) (p.217): `q(τ, θ) = 1` if `θ ≥ p(τ)`, `0` otherwise. -/
noncomputable def SeqEnv.optQ (E : SeqEnv τlo τhi θlo θhi) (τ θ : ℝ) : ℝ :=
  if E.p τ ≤ θ then 1 else 0

/-- The payment of the lowest type in the optimal mechanism, (11.12) (p.218):
`t(τ̲, θ̲) = ∫_{p(τ̲)}^{θ̄} θ̂ f(θ̂|τ̲) dθ̂ − p(τ̲)[1 − F(p(τ̲)|τ̲)] + θ̲ q(τ̲, θ̲)`,
with `q` the optimal allocation rule (11.10). -/
noncomputable def SeqEnv.optTlo (E : SeqEnv τlo τhi θlo θhi) : ℝ :=
  (∫ θ' in E.p τlo..θhi, θ' * E.f θ' τlo) - E.p τlo * (1 - E.F (E.p τlo) τlo) +
    θlo * E.optQ τlo θlo

/-- The option fee `t₀(τ)` of the optimal mechanism: `t₀` of Proposition 11.5 for the allocation
rule (11.10) and the lowest-type payment (11.12). -/
noncomputable def SeqEnv.optT0 (E : SeqEnv τlo τhi θlo θhi) (τ : ℝ) : ℝ :=
  E.t0 E.optQ E.optTlo τ

/-- The optimal payment rule (11.11) (p.218): `t(τ, θ) = t₀(τ) + p(τ)` if `θ ≥ p(τ)`, and
`t₀(τ)` otherwise, with `t₀` as in `SeqEnv.optT0`. -/
noncomputable def SeqEnv.optT (E : SeqEnv τlo τhi θlo θhi) (τ θ : ℝ) : ℝ :=
  if E.p τ ≤ θ then E.optT0 τ + E.p τ else E.optT0 τ

end MechanismDesign.Dynamic
