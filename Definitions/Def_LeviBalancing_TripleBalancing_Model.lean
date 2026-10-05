import Mathlib

open MeasureTheory ProbabilityTheory

namespace LeviBalancing.TripleBalancing

/-- The data of the stochastic lot-sizing problem of Levi, Pál, Roundy & Shmoys (2007), §2 and the
preamble of §6 (pp. 288–289, 299): a probability space `μ` with an information filtration `ℱ`
(`ℱ t` is the information available at the beginning of period `t`, i.e. the information set
`f_t`), a horizon of `T` periods numbered `1, …, T`, a fixed ordering cost `K ≥ 0` (the per-unit
ordering cost is `c_t = 0`, the lead time is `L = 0`, the discount factor is `α = 1`), holding costs
`h t ≥ 0`, backlogging penalties `p t ≥ 0`, a deterministic initial inventory level `x₁`, and
nonnegative demands `D t`.  The §6 assumption that the demand of period `t` is known at the
beginning of period `t` is `D_known`: `D t` is `ℱ t`-measurable.  Values at indices outside
`1, …, T` are never used. -/
structure LotSizingModel (Ω : Type*) [mΩ : MeasurableSpace Ω] where
  /-- the probability measure -/
  μ : Measure Ω
  isProb : IsProbabilityMeasure μ
  /-- `ℱ t`: the information available at the beginning of period `t` -/
  ℱ : Filtration ℕ mΩ
  /-- number of periods -/
  T : ℕ
  /-- fixed ordering cost -/
  K : ℝ
  K_nonneg : 0 ≤ K
  /-- per-unit holding cost of period `t` -/
  h : ℕ → ℝ
  /-- per-unit backlogging penalty of period `t` -/
  p : ℕ → ℝ
  h_nonneg : ∀ t, 0 ≤ h t
  p_nonneg : ∀ t, 0 ≤ p t
  /-- initial inventory level at the beginning of period 1 -/
  x₁ : ℝ
  /-- demand of period `t` -/
  D : ℕ → Ω → ℝ
  D_nonneg : ∀ t ω, 0 ≤ D t ω
  /-- the demand of period `t` is known at the beginning of period `t` -/
  D_known : ∀ t, Measurable[ℱ t] (D t)

attribute [instance] LotSizingModel.isProb

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The demand path `ω ↦ (D_t(ω))_t`. -/
def LotSizingModel.demandPath (M : LotSizingModel Ω) (ω : Ω) : ℕ → ℝ := fun t => M.D t ω

/-- `I` is a version of the paper's conditional joint distribution `I_s = I_s(f_s)` of the demands
given the information at the beginning of period `s` (p. 288), with the properties the paper
assumes of it:
1. each `I s ω` is a probability measure on demand paths;
2. `ω ↦ I s ω A` is `ℱ s`-measurable (it is determined by the information set `f_s`);
3. it is a regular conditional distribution of the demand path given `ℱ s`:
   `μ (B ∩ {D ∈ A}) = ∫_B I s ω A dμ` for every `ℱ s`-measurable `B`;
4. the demand `D_s` is known deterministically under `I_s` (§6, p. 299);
5. demands are nonnegative under `I_s`;
6. the conditional expectation `E[D_t | f_s]` is finite for `1 ≤ s ≤ t ≤ T` (p. 288). -/
def LotSizingModel.IsCondDemandLaw (M : LotSizingModel Ω) (I : ℕ → Kernel Ω (ℕ → ℝ)) : Prop :=
  (∀ s, IsMarkovKernel (I s)) ∧
  (∀ s (A : Set (ℕ → ℝ)), MeasurableSet A → Measurable[M.ℱ s] (fun ω => I s ω A)) ∧
  (∀ s (A : Set (ℕ → ℝ)) (B : Set Ω), MeasurableSet A → MeasurableSet[M.ℱ s] B →
      M.μ (B ∩ M.demandPath ⁻¹' A) = ∫⁻ ω in B, I s ω A ∂M.μ) ∧
  (∀ s ω, ∀ᵐ d ∂(I s ω), d s = M.D s ω) ∧
  (∀ s ω, ∀ᵐ d ∂(I s ω), ∀ t, 0 ≤ d t) ∧
  (∀ s t ω, 1 ≤ s → s ≤ t → t ≤ M.T → Integrable (fun d : ℕ → ℝ => d t) (I s ω))

end LeviBalancing.TripleBalancing
