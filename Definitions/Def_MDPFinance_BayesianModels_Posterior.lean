import Mathlib
import Definitions.Def_MDPFinance_BayesianModels_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MDPFinance.BayesianModels

variable {EX Θ A Z : Type*} [MeasurableSpace EX] [MeasurableSpace Θ] [MeasurableSpace A]
  [MeasurableSpace Z]

/-- The **posterior/filter process** `(μ_n)` of a Bayesian Model (Bäuerle–Rieder, p. 159-160,
PDF 172-173, `μ_n(C|h̃_n) := ℙ^π_x(θ ∈ C \mid X_0,A_0,Z_1,\dots,X_n)`): a family of probability
measures on `Θ`, one for every stage `n` and observable history `h̃_n = (xs,as,zs)`, non-
anticipating in the history, agreeing with the prior at `n = 0`, and satisfying the one-step
Bayes update `μ_{n+1}(C|h̃_n,a_n,z_{n+1}) = [∫_C q_Z(x_n,θ,a_n,z_{n+1}) dμ_n(h̃_n)(θ)] /
[∫_Θ q_Z(x_n,θ,a_n,z_{n+1}) dμ_n(h̃_n)(θ)]` (Bäuerle–Rieder, Example 5.2.4, Eq. (5.7), p. 155,
PDF 168, the Bayes operator `Φ` specialized to the Bayesian Model). Existence of `μ_n` as a
genuine regular conditional probability is the book's own standing assumption (general
conditioning theory, not reproved here); it is *data*, characterized by its defining properties,
exactly as `MDPFinance.POMDP.FilterData.Phi`/`hPhi` (chunk `05a`) bundles the general Bayes
operator. Lemma 5.4.1's explicit `n`-fold product formula is then a genuine consequence of
`hmu0`/`hmu_rec` by induction (see `Thm_MDPFinance_BayesianModels_lemma_5_4_1.lean`), not built
into this definition. -/
structure BayesModel.Posterior (M : BayesModel EX Θ A Z) where
  mu : (n : ℕ) → (ℕ → EX) → (ℕ → A) → (ℕ → Z) → Measure Θ
  hmu_prob : ∀ n xs as zs, IsProbabilityMeasure (mu n xs as zs)
  hmu_dep : ∀ n xs xs' as as' zs zs', (∀ i ≤ n, xs i = xs' i) → (∀ i < n, as i = as' i) →
    (∀ i, 1 ≤ i → i ≤ n → zs i = zs' i) → mu n xs as zs = mu n xs' as' zs'
  hmu0 : ∀ xs as zs, mu 0 xs as zs = M.Q0
  /-- `h̃_n ↦ μ_n(C|h̃_n)` is measurable (`μ_n` is a stochastic kernel from `H̃_n` to `Θ`). -/
  hmu_meas : ∀ n (C : Set Θ), MeasurableSet C →
    Measurable fun p : (ℕ → EX) × (ℕ → A) × (ℕ → Z) => mu n p.1 p.2.1 p.2.2 C
  /-- The one-step Bayes update (5.7), required wherever it defines a probability measure, i.e.
  wherever the normalizing constant `∫ q_Z(x_n,θ,a_n,z_{n+1}) μ_n(dθ)` is positive and finite
  (elsewhere the book's quotient is `0/0` or `∞/∞`; such `z_{n+1}` form a null set for the
  predictive law of `Z_{n+1}`). -/
  hmu_rec : ∀ n xs as zs,
    0 < (∫⁻ θ, ENNReal.ofReal (M.qZ (xs n) θ (as n) (zs (n + 1))) ∂(mu n xs as zs)) →
    (∫⁻ θ, ENNReal.ofReal (M.qZ (xs n) θ (as n) (zs (n + 1))) ∂(mu n xs as zs)) < ⊤ →
    ∀ (C : Set Θ), MeasurableSet C →
    mu (n + 1) xs as zs C =
      (∫⁻ θ in C, ENNReal.ofReal (M.qZ (xs n) θ (as n) (zs (n + 1))) ∂(mu n xs as zs)) /
        (∫⁻ θ, ENNReal.ofReal (M.qZ (xs n) θ (as n) (zs (n + 1))) ∂(mu n xs as zs))

end MDPFinance.BayesianModels
