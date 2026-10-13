import Mathlib
import Definitions.Def_StochApproxDyn_MartingaleNoise_Interpolation

namespace StochApproxDyn.MartingaleNoise

open Filter Topology
open scoped ENNReal

/-- The quantity inside assumption A1 (Benaïm 1999, §4.1, p. 12):
`sup { ‖∑_{i=n}^{k-1} γ_{i+1} U_{i+1}‖ : k = n+1, …, m(τ_n + T) }`,
valued in `[0, ∞]`. The range of `k` is finite; when it is empty (`m(τ_n + T) ≤ n`) the
supremum is `0`. -/
noncomputable def a1Sup {d : ℕ} (γ : ℕ → ℝ) (U : ℕ → EuclideanSpace ℝ (Fin d)) (n : ℕ)
    (T : ℝ) : ℝ≥0∞ :=
  (Finset.Ioc n (stepIndex γ (StochApproxDyn.Interpolation.tau γ n + T))).sup fun k =>
    ‖∑ i ∈ Finset.Ico n k, γ (i + 1) • U (i + 1)‖ₑ

/-- Assumption A1 (§4.1, p. 12), first form: for all `T > 0`,
`lim_{n→∞} sup { ‖∑_{i=n}^{k-1} γ_{i+1} U_{i+1}‖ : k = n+1, …, m(τ_n + T) } = 0`. -/
def IsA1 {d : ℕ} (γ : ℕ → ℝ) (U : ℕ → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ T : ℝ, 0 < T → Tendsto (fun n : ℕ => a1Sup γ U n T) atTop (𝓝 0)

/-- `Δ(t, T) = sup_{0 ≤ h ≤ T} ‖∫_t^{t+h} Ū(s) ds‖`, Eq. (10) (§4.1, p. 12), valued in
`[0, ∞]` (it is finite under the standing assumptions, since `Ū` takes finitely many values on
`[t, t + T]`). -/
noncomputable def noiseDev {d : ℕ} (γ : ℕ → ℝ) (U : ℕ → EuclideanSpace ℝ (Fin d)) (t T : ℝ) :
    ℝ≥0∞ :=
  ⨆ h ∈ Set.Icc (0 : ℝ) T, ‖∫ s in t..(t + h), noisePath γ U s‖ₑ

/-- Assumption A1 (§4.1, p. 12), second ("equivalent") form: for all `T > 0`,
`lim_{t→∞} Δ(t, T) = 0`. -/
def IsA1Delta {d : ℕ} (γ : ℕ → ℝ) (U : ℕ → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ T : ℝ, 0 < T → Tendsto (fun t : ℝ => noiseDev γ U t T) atTop (𝓝 0)

end StochApproxDyn.MartingaleNoise
