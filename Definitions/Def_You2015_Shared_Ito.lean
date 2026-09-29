import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace You2015.Shared

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- A simple adapted `E`-valued integrand on `[0, T]`: a partition
`0 = t₀ ≤ t₁ ≤ ⋯ ≤ t_p = T` and square-integrable random vectors `ξᵢ`, each
`𝓕_{tᵢ}`-measurable; the process is `∑ᵢ ξᵢ 1_{(tᵢ, tᵢ₊₁]}`. -/
structure SimpleIntegrand (E : Type*) [NormedAddCommGroup E] (𝓕 : Filtration ℝ≥0 mΩ)
    (P : Measure Ω) (T : ℝ≥0) where
  p : ℕ
  t : Fin (p + 1) → ℝ≥0
  mono : Monotone t
  start : t 0 = 0
  finish : t (Fin.last p) = T
  ξ : Fin p → Ω → E
  meas : ∀ i, StronglyMeasurable[𝓕 (t i.castSucc)] (ξ i)
  sq : ∀ i, ∫⁻ ω, ‖ξ i ω‖ₑ ^ 2 ∂P < ⊤

namespace SimpleIntegrand

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {𝓕 : Filtration ℝ≥0 mΩ} {P : Measure Ω} {T : ℝ≥0}

/-- The value `∑ᵢ 1_{(tᵢ, tᵢ₊₁]}(s) ξᵢ(ω)` of a simple integrand. -/
noncomputable def eval (H : SimpleIntegrand E 𝓕 P T) (s : ℝ≥0) (ω : Ω) : E :=
  ∑ i : Fin H.p, if H.t i.castSucc < s ∧ s ≤ H.t i.succ then H.ξ i ω else 0

/-- The elementary stochastic integral `∫₀ᵘ H dW = ∑ᵢ (W(tᵢ₊₁ ∧ u) − W(tᵢ ∧ u)) ξᵢ`
against a real process `W`. -/
noncomputable def integral (H : SimpleIntegrand E 𝓕 P T) (W : ℝ≥0 → Ω → ℝ) (u : ℝ≥0)
    (ω : Ω) : E :=
  ∑ i : Fin H.p, (W (min (H.t i.succ) u) ω - W (min (H.t i.castSucc) u) ω) • H.ξ i ω

end SimpleIntegrand

/-- `J(t) = ∫₀ᵗ H(s) dW(s)`, `t ≥ 0`, is an L² Itô integral process of the `E`-valued integrand
`H` against the real process `W`: `H` is progressively measurable for `{𝓕_t}` with
`E ∫₀ᵀ |H(s)|² ds < ∞` for every `T`, `J` is adapted, and for every horizon `T` some sequence
of simple adapted integrands `Hₖ` on `[0, T]` satisfies `E ∫₀ᵀ |Hₖ − H|² ds → 0` and, for every
`t ∈ [0, T]`, `E |∫₀ᵗ Hₖ dW − J(t)|² → 0`. Expectations and time integrals are lower Lebesgue
integrals in `[0, ∞]`. -/
def IsItoIntegral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (H J : ℝ≥0 → Ω → E) :
    Prop :=
  IsStronglyProgressive 𝓕 H ∧
    (∀ T : ℝ≥0, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ‖H s.toNNReal ω‖ₑ ^ 2 ∂volume ∂P < ⊤) ∧
    StronglyAdapted 𝓕 J ∧
    ∀ T : ℝ≥0, ∃ Hs : ℕ → SimpleIntegrand E 𝓕 P T,
      Tendsto (fun k => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          ‖(Hs k).eval s.toNNReal ω - H s.toNNReal ω‖ₑ ^ 2 ∂volume ∂P) atTop (𝓝 0) ∧
      ∀ t ≤ T, Tendsto (fun k => ∫⁻ ω, ‖(Hs k).integral W t ω - J t ω‖ₑ ^ 2 ∂P)
          atTop (𝓝 0)

end You2015.Shared
