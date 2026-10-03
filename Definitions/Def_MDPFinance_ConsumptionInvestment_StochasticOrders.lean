import Mathlib

open MeasureTheory

namespace MDPFinance.ConsumptionInvestment

/-- The increasing concave order on measures on `ℝ` (Bäuerle–Rieder, Definition B.3.9c, p. 361,
PDF 368): `μ ≤_icv ν` iff `∫ f dμ ≤ ∫ f dν` for every increasing, concave `f` for which both
integrals exist. Restated from `MDPFinance.StructuredModels`'s `≤_st`/`≤_cx`/`≤_cv` triple
(chunk `02c`), which does not itself include this order. -/
def LEIncreasingConcaveOrder (μ ν : Measure ℝ) : Prop :=
  ∀ f : ℝ → ℝ, Monotone f → ConcaveOn ℝ Set.univ f → Integrable f μ → Integrable f ν →
    ∫ x, f x ∂μ ≤ ∫ x, f x ∂ν

/-- A finite Markov chain with transition matrix `p` on a linearly ordered state space `EY` is
stochastically monotone (Bäuerle–Rieder, Definition B.3.13, p. 362-363, PDF 369, specialized to
a finite chain via transition probabilities) if `j ↦ Σ_k p_{jk} v(k)` is increasing for every
increasing `v : EY → ℝ`. -/
def IsStochasticallyMonotoneChain {EY : Type*} [Fintype EY] [Preorder EY] (p : EY → EY → ℝ) :
    Prop :=
  ∀ v : EY → ℝ, Monotone v → Monotone (fun j => ∑ k, p j k * v k)

end MDPFinance.ConsumptionInvestment
