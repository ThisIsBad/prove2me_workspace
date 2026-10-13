import Mathlib

namespace StochApproxDyn.SubgaussianNoise

open MeasureTheory
open scoped InnerProductSpace

/-- Subgaussian noise with a given constant `Γ` (Benaïm 1999, §4.2, p. 16): for every `n ≥ 0`
and every `θ ∈ ℝ^d`, `exp ⟨θ, U_{n+1}⟩` is integrable and
`E(exp ⟨θ, U_{n+1}⟩ | ℱ_n) ≤ exp((Γ/2)‖θ‖²)` almost surely.
The integrability clause makes the conditional expectation the genuine one (Lean's `condExp`
of a non-integrable function is `0`, which would make the bound vacuous). -/
def IsSubgaussianWith {d : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω)
    (ℱ : Filtration ℕ m0) (U : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (Γ : ℝ) : Prop :=
  ∀ (n : ℕ) (θ : EuclideanSpace ℝ (Fin d)),
    Integrable (fun ω => Real.exp ⟪θ, U (n + 1) ω⟫_ℝ) P ∧
    P[fun ω => Real.exp ⟪θ, U (n + 1) ω⟫_ℝ | ℱ n] ≤ᵐ[P] fun _ => Real.exp (Γ / 2 * ‖θ‖ ^ 2)

/-- The sequence `{U_n}` is **subgaussian** (Benaïm 1999, §4.2, p. 16) if there exists a positive
number `Γ` such that for all `θ ∈ ℝ^d` and all `n`,
`E(exp ⟨θ, U_{n+1}⟩ | ℱ_n) ≤ exp((Γ/2)‖θ‖²)`. -/
def IsSubgaussian {d : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω)
    (ℱ : Filtration ℕ m0) (U : ℕ → Ω → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∃ Γ : ℝ, 0 < Γ ∧ IsSubgaussianWith P ℱ U Γ

end StochApproxDyn.SubgaussianNoise
