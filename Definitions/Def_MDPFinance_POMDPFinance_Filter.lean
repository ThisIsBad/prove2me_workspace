import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MDPFinance.POMDPFinance

/-- The financial-market half of a stationary Partially Observable Markov Decision Model for
Chapter 6 (Bäuerle–Rieder, p. 177-178, PDF 190-191): the unobservable factor `Y` (state space
`EY`) drives the relative-risk vector `Z ∈ ℝ^d` via a density `q_R(y,\cdot)` (w.r.t. a σ-finite
reference `lam` on `ℝ^d`) and evolves by its own stochastic kernel `Q^Y`, matching
`Q^{Z,Y}(B×C|x,y,a) = Q^R(B|y)Q^Y(C|y)` (p. 175-177): the joint kernel does not depend on `(x,a)`
at all, only on `y`. `Q_0` is the prior law of `Y_0`. Only the observation kernel `Q^R` is
required to have a density: it is the likelihood of the observed return, which is all the Bayes
operator below uses; `Q^Y` is a kernel, so that the Bayesian sub-models of the chapter (a constant
hidden parameter, `Q^Y(·|y) = δ_y`, which has no density with respect to a σ-finite measure on an
uncountable `E_Y`) are instances. -/
structure FilterMarket (EY : Type*) [MeasurableSpace EY] (d : ℕ) where
  lam : Measure (Fin d → ℝ)
  hlam_sigmaFinite : SigmaFinite lam
  qR : EY → (Fin d → ℝ) → ℝ
  hqR_meas : Measurable (Function.uncurry qR)
  hqR_nonneg : ∀ y z, 0 ≤ qR y z
  /-- `Q^R(·|y)` is a probability measure (the density integrates to one). -/
  hqR_prob : ∀ y, ∫⁻ z, ENNReal.ofReal (qR y z) ∂lam = 1
  /-- The relative risk takes values in `Z = [-1,∞)^d` (p. 176). -/
  hqR_supp : ∀ y, ∀ᵐ z ∂(lam.withDensity fun z => ENNReal.ofReal (qR y z)), ∀ j, -1 ≤ z j
  /-- The transition kernel `Q^Y` of the hidden Markov process `(Y_n)`, a stochastic kernel. -/
  QY : Kernel EY EY
  isMarkovQY : IsMarkovKernel QY
  Q0 : Measure EY
  isProbQ0 : IsProbabilityMeasure Q0

variable {EY : Type*} [MeasurableSpace EY] {d : ℕ}

/-- The **predictive law of the next return** `Z` given current belief `ρ` about `Y`: the mixture
`∫ (\text{law with density } q_Z(y,\cdot)) \, ρ(dy)`. Used to render every double integral
`∫∫ f(z) Q^R(dz|y) ρ(dy)` of this chapter (e.g. Theorem 6.1.1b) as the single integral
`∫ f(z) d(\text{predictive } ρ)(z)`, matching `MDPFinance.BayesianModels`'s (chunk `05b`) mixture
convention `(S.muHat i).bind fun θ => ...`. -/
noncomputable def FilterMarket.predictive (M : FilterMarket EY d) (ρ : Measure EY) :
    Measure (Fin d → ℝ) :=
  ρ.bind fun y => M.lam.withDensity fun z => ENNReal.ofReal (M.qR y z)

/-- The law `Q^R(·|y)` of `R(y)`, the relative risk given the hidden state `y`. -/
noncomputable def FilterMarket.law (M : FilterMarket EY d) (y : EY) : Measure (Fin d → ℝ) :=
  M.lam.withDensity fun z => ENNReal.ofReal (M.qR y z)

/-- The **Bayes filter update** `Φ(ρ,z)` (Bäuerle–Rieder, p. 177: "The Bayes operator `Φ` depends
only on `ρ ∈ ℙ(E_Y)` and `z ∈ Z`", a genuine simplification of the general `Φ(x,ρ,a,x')` of
`MDPFinance.POMDP.FilterData` (chunk `05a`) forced by `Q^{Z,Y}` not depending on `(x,a)`, restated
here rather than imported per this chunk's own file-ownership boundary): the posterior law of
`Y_{n+1}` given prior belief `ρ` about `Y_n` and observed return `z`, `Φ` is *data*, characterized
by the ratio formula it must satisfy (the numerator is `∫ q_R(y,z) Q^Y(C|y) ρ(dy)`, the joint
weight of the observed `z` and `Y_{n+1} ∈ C` under `y ~ ρ`; the denominator is the predictive
density of `z`, matching `FilterMarket.predictive`), wherever that formula defines a probability
measure. -/
structure FilterOp (M : FilterMarket EY d) where
  Phi : Measure EY → (Fin d → ℝ) → Measure EY
  hPhi_prob : ∀ (ρ : Measure EY) z, IsProbabilityMeasure ρ → IsProbabilityMeasure (Phi ρ z)
  /-- `Φ` is a stochastic kernel: measurable in `(ρ,z)`. -/
  hPhi_meas : Measurable (Function.uncurry Phi)
  /-- The Bayes update, required wherever it defines a probability measure, i.e. wherever the
  predictive density `∫ q_R(y,z) ρ(dy)` of `z` is positive and finite (elsewhere the book's
  quotient is `0/0` or `∞/∞`; such `z` form a null set for the predictive law). -/
  hPhi : ∀ (ρ : Measure EY) z,
    0 < (∫⁻ y, ENNReal.ofReal (M.qR y z) ∂ρ) → (∫⁻ y, ENNReal.ofReal (M.qR y z) ∂ρ) < ⊤ →
    ∀ (C : Set EY), MeasurableSet C →
    Phi ρ z C =
      (∫⁻ y, ENNReal.ofReal (M.qR y z) * M.QY y C ∂ρ) / (∫⁻ y, ENNReal.ofReal (M.qR y z) ∂ρ)

/-- The **filter process** `μ_n(\cdot|h_n)`, restricted to its dependence on the observable
return history `z_1,\dots,z_n` alone (Bäuerle–Rieder, p. 177: `F_n = F^S_n = σ(R_1,\dots,R_n)`,
so a decision rule — and hence the filter itself, being `F_n`-measurable — depends on the history
only through the observed returns, not through wealth or past actions, unlike the general
`MDPFinance.POMDP.FilterData.mu` (chunk `05a`) which threads the full `(xs,as)` pair): `μ_0 :=
Q_0`, `μ_{n+1}(\cdot|z_1,\dots,z_{n+1}) := Φ(μ_n(\cdot|z_1,\dots,z_n), z_{n+1})`. `zs : ℕ →
(Fin d → ℝ)` is padded (`zs 0` unused junk, indices start at `1`, as elsewhere in this series). -/
noncomputable def FilterOp.mu (M : FilterMarket EY d) (Fd : FilterOp M) :
    (n : ℕ) → (ℕ → (Fin d → ℝ)) → Measure EY
  | 0, _ => M.Q0
  | (n + 1), zs => Fd.Phi (FilterOp.mu M Fd n zs) (zs (n + 1))

end MDPFinance.POMDPFinance
