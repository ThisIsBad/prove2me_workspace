import Mathlib
import Definitions.Def_PoissonDirichlet_Ratio_Setting
open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.Wendel

/-- (31), first expression, 0-based: `Aseq v k = (v 0 + ⋯ + v (k-1)) / v k` is
`A_k = (V_1 + ⋯ + V_k) / V_{k+1}`; in particular `Aseq v 0 = 0 = A_0`. -/
noncomputable def Aseq (v : ℕ → ℝ) (k : ℕ) : ℝ := (∑ i ∈ Finset.range k, v i) / v k

/-- (32), first expression, 0-based: `Sigseq v k = (v (k+1) + v (k+2) + ⋯) / v k` is
`Σ_{k+1} = (V_{k+2} + V_{k+3} + ⋯) / V_{k+1}`. -/
noncomputable def Sigseq (v : ℕ → ℝ) (k : ℕ) : ℝ := (∑' j, v (k + 1 + j)) / v k

/-- (33): `φ_α(λ) = α ∫_1^∞ e^{-λx} x^{-α-1} dx`. -/
noncomputable def phi (α l : ℝ) : ℝ :=
  α * ∫ x in Set.Ioi (1 : ℝ), Real.exp (-l * x) * x ^ (-α - 1)

/-- (34), first expression: `ψ_α(λ) = 1 + α ∫_0^1 (1 - e^{-λx}) x^{-α-1} dx`. -/
noncomputable def psi (α l : ℝ) : ℝ :=
  1 + α * ∫ x in Set.Ioc (0 : ℝ) 1, (1 - Real.exp (-l * x)) * x ^ (-α - 1)

/-- The `k`-fold additive convolution power of a measure on `ℝ`: the law of the sum of `k`
independent random variables with law `μ` (the Dirac mass at `0` for `k = 0`). -/
noncomputable def convPow (μ : Measure ℝ) (k : ℕ) : Measure ℝ :=
  (fun ν => ν ∗ μ)^[k] (Measure.dirac 0)

/-- `C⁻¹ Λ_α(dx) 1(x > 1) = α x^{-α-1} dx 1(x > 1)`, the law in Lemma 24 (ii) and (66). -/
noncomputable def tailLaw (α : ℝ) : Measure ℝ :=
  volume.withDensity ((Set.Ioi (1 : ℝ)).indicator fun x => ENNReal.ofReal (α * x ^ (-α - 1)))

/-- Arrival times of a unit-rate Poisson process from its interarrival times, 0-based:
`arrival ε k ω = ε 0 ω + ⋯ + ε k ω` is `X_{k+1} = ε_1 + ⋯ + ε_{k+1}` of (28). -/
def arrival {Ω : Type*} (ε : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), ε i ω

/-- The ranked points of a PRM `Λ_α` on `(0, ∞)` with `Λ_α(x, ∞) = C x^{-α}`, represented
through arrival times as in (27)–(28): `prmPoint α C ε k = (C / X_{k+1})^{1/α}` is `Δ_{k+1}`. -/
noncomputable def prmPoint {Ω : Type*} (α C : ℝ) (ε : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  (C / arrival ε k ω) ^ (1 / α)

end PoissonDirichlet.Wendel
