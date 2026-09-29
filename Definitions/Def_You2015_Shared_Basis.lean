import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace You2015.Shared

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The **usual conditions** on a filtration `{𝓕_t}_{t ≥ 0}` of `(Ω, 𝓕, P)`: the filtration is
increasing (built into `Filtration`), right-continuous, `𝓕_t = ⋂_{s > t} 𝓕_s` for every `t ≥ 0`
(the infimum of σ-algebras), and `𝓕_0` contains every `P`-null set. Because `𝓕_0 ⊆ 𝓕`, the
second clause also makes `(Ω, 𝓕, P)` complete. -/
def UsualConditions (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) : Prop :=
  (∀ t : ℝ≥0, 𝓕 t = ⨅ s ∈ Set.Ioi t, 𝓕 s) ∧
    ∀ A : Set Ω, P A = 0 → MeasurableSet[𝓕 0] A

/-- `w = (w_1, …, w_m)ᵀ` is an `m`-dimensional `{𝓕_t}`-Brownian motion: each coordinate is a
standard real Brownian motion (Mathlib's `IsBrownianReal`: Gaussian increments with variance
the elapsed time, independent increments, `w(0) = 0` a.s., a.s. continuous paths), the `m`
coordinate processes are mutually independent, `w(t)` is `𝓕_t`-measurable for each `t`, and
every increment `w(s + t) − w(s)` is independent of `𝓕_s`. -/
structure IsFBrownian {m : ℕ} (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ)
    (w : ℝ≥0 → Ω → (Fin m → ℝ)) : Prop where
  brownian : ∀ k : Fin m, IsBrownianReal (fun t ω => w t ω k) P
  indep_coord : iIndepFun (fun (k : Fin m) (ω : Ω) (t : ℝ≥0) => w t ω k) P
  adapted : ∀ t : ℝ≥0, Measurable[𝓕 t] (w t)
  indep_incr : ∀ s t : ℝ≥0,
    Indep (MeasurableSpace.comap (fun ω => w (s + t) ω - w s ω) inferInstance) (𝓕 s) P

/-- `Γ = (γ_ij)_{N × N}` is a generator (Q-matrix) on `S = {0, …, N − 1}`: the off-diagonal
transition rates are nonnegative and `γ_ii = −∑_{j ≠ i} γ_ij` (zero row sums). -/
def IsGenerator {N : ℕ} (Γ : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  (∀ i j, i ≠ j → 0 ≤ Γ i j) ∧ ∀ i, Γ i i = -∑ j ∈ Finset.univ.erase i, Γ i j

/-- `r` is a right-continuous `{𝓕_t}`-Markov chain on `S = Fin N` with generator `Γ`:
every path is right-continuous (for a finite state space: constant on some `[t, t + ε)`),
`r(t)` is `𝓕_t`-measurable, and for all `s, t ≥ 0` and every state `j`,
`P(r(s + t) = j | 𝓕_s) = (e^{tΓ})_{r(s), j}` almost surely (time-homogeneous transition matrix
`P(t) = e^{tΓ}`, i.e. `P(Δ) = I + ΓΔ + o(Δ)`). -/
structure IsFMarkovChain {N : ℕ} (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ)
    (Γ : Matrix (Fin N) (Fin N) ℝ) (r : ℝ≥0 → Ω → Fin N) : Prop where
  right_cont : ∀ ω t, ∃ ε > 0, ∀ s, t ≤ s → s < t + ε → r s ω = r t ω
  adapted : ∀ t : ℝ≥0, Measurable[𝓕 t] (r t)
  markov : ∀ s t : ℝ≥0, ∀ j : Fin N,
    P[(fun ω => if r (s + t) ω = j then (1 : ℝ) else 0) | 𝓕 s]
      =ᵐ[P] fun ω => NormedSpace.exp ((t : ℝ) • Γ) (r s ω) j

/-- The stochastic basis of the controlled hybrid SDE (2.1): a filtration `{𝓕_t}` satisfying
the usual conditions, an `m`-dimensional `{𝓕_t}`-Brownian motion `w`, and a right-continuous
`{𝓕_t}`-Markov chain `r` on `Fin N` with generator `Γ`, started at `r(0) = r₀` (a.s.), with the
chain `r(·)` independent of the Brownian motion `w(·)` (as path-valued random variables). -/
structure HybridSetup (P : Measure Ω) (m N : ℕ) (Γ : Matrix (Fin N) (Fin N) ℝ)
    (r₀ : Fin N) where
  𝓕 : Filtration ℝ≥0 mΩ
  w : ℝ≥0 → Ω → (Fin m → ℝ)
  r : ℝ≥0 → Ω → Fin N
  usual : UsualConditions P 𝓕
  brownian : IsFBrownian P 𝓕 w
  markov : IsFMarkovChain P 𝓕 Γ r
  init : ∀ᵐ ω ∂P, r 0 ω = r₀
  indep : IndepFun (fun ω t => r t ω) (fun ω t => w t ω) P

end You2015.Shared
