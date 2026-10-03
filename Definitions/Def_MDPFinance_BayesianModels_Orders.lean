import Mathlib

open MeasureTheory

namespace MDPFinance.BayesianModels

/-- The **likelihood ratio order** on real densities (Bäuerle–Rieder, Definition B.3.5, p. 360,
PDF 366, applied directly to two densities `f`, `g` w.r.t. a common dominating measure, as the
book itself writes `q_Z(\cdot|θ,a) ≤_{lr} q_Z(\cdot|θ',a)` and `\hat μ(\cdot|i) ≤_{lr}
\hat μ(\cdot|i')` for densities rather than for the underlying random variables): `f ≤_{lr} g` iff
`f(t) g(s) ≤ f(s) g(t)` for all `s ≤ t`. Distinct from `MDPFinance.StructuredModels.
LEStochasticOrder`/`LEConcaveOrder` (chunk `02c`), which compare measures via test-function
expectations, not densities via a ratio-monotonicity condition. -/
def LikelihoodRatioOrder (f g : ℝ → ℝ) : Prop :=
  ∀ s t : ℝ, s ≤ t → f t * g s ≤ f s * g t

/-- `μ ≤_{lr} μ'` for two measures on `ℝ` with densities w.r.t. a common dominating measure `ρ`
(Bäuerle–Rieder, Definition B.3.5, p. 360, PDF 366): *some* versions `f`, `g` of the densities
satisfy `f(t) g(s) ≤ f(s) g(t)` for all `s ≤ t`. Stated on the measures, so that it does not
depend on the versions chosen (the book's `\hat μ(\cdot|i) ≤_{lr} \hat μ(\cdot|i')`, p. 164). -/
def LRMeasure (ρ μ μ' : Measure ℝ) : Prop :=
  ∃ f g : ℝ → ℝ, Measurable f ∧ Measurable g ∧ (∀ θ, 0 ≤ f θ) ∧ (∀ θ, 0 ≤ g θ) ∧
    μ = ρ.withDensity (fun θ => ENNReal.ofReal (f θ)) ∧
    μ' = ρ.withDensity (fun θ => ENNReal.ofReal (g θ)) ∧ LikelihoodRatioOrder f g

/-- **MTP2** (multivariate total positivity of order 2) (Bäuerle–Rieder, Definition A.3.3, p. 353,
PDF 359): a function `f : ℝ^d → ℝ_{≥0}` is MTP2 if `f(x) f(y) ≤ f(x ∧ y) f(x ∨ y)` for all
`x, y`, where `∧`, `∨` are the componentwise min/max. Specialized here to `d = 2` (`ℝ × ℝ`,
matching Lemma 5.4.9's `q_Z(z|θ,a)` as a function of the pair `(z,θ)`), using `Prod`'s pointwise
lattice structure for `⊓`/`⊔`. -/
def IsMTP2 (f : ℝ × ℝ → ℝ) : Prop :=
  ∀ x y : ℝ × ℝ, f x * f y ≤ f (x ⊓ y) * f (x ⊔ y)

end MDPFinance.BayesianModels
