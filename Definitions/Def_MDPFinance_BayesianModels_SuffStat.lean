import Mathlib
import Definitions.Def_MDPFinance_BayesianModels_Model
import Definitions.Def_MDPFinance_BayesianModels_Posterior

open MeasureTheory ProbabilityTheory

namespace MDPFinance.BayesianModels

variable {EX Θ A Z : Type*} [MeasurableSpace EX] [MeasurableSpace Θ] [MeasurableSpace A]
  [MeasurableSpace Z]

/-- Definition 5.4.3 (Bäuerle–Rieder, p. 160-161, PDF 173-174): a **sufficient statistic** for
`(μ_n)` is a sequence `t = (t_n)` of measurable maps `t_n : H̃_n → I` (represented as functions of
the padded history triple `(xs,as,zs)`, non-anticipating exactly as a decision rule is) for which
there exists a transition kernel `μ̂` from `I` to `Θ` with `μ_n(C|h̃_n) = μ̂(C|t_n(h̃_n))` for all
`h̃_n`, `C ∈ B(Θ)`, `n`. -/
structure SuffStat (M : BayesModel EX Θ A Z) (Pf : M.Posterior) (I : Type*) [MeasurableSpace I]
    where
  t : (n : ℕ) → (ℕ → EX) → (ℕ → A) → (ℕ → Z) → I
  ht_meas : ∀ n, Measurable fun p : (ℕ → EX) × (ℕ → A) × (ℕ → Z) => t n p.1 p.2.1 p.2.2
  ht_dep : ∀ n xs xs' as as' zs zs', (∀ i ≤ n, xs i = xs' i) → (∀ i < n, as i = as' i) →
    (∀ i, 1 ≤ i → i ≤ n → zs i = zs' i) → t n xs as zs = t n xs' as' zs'
  muHat : Kernel I Θ
  hmuHat_prob : ∀ i, IsProbabilityMeasure (muHat i)
  ht_suff : ∀ n xs as zs (C : Set Θ), MeasurableSet C →
    (Pf.mu n xs as zs) C = muHat (t n xs as zs) C

variable {I : Type*} [MeasurableSpace I] {M : BayesModel EX Θ A Z} {Pf : M.Posterior}

/-- Definition 5.4.5 (Bäuerle–Rieder, p. 162, PDF 175): `(t_n)` is a **sequential sufficient
statistic** if its next value is a measurable function `Φ̂` of only the current observable state,
the current statistic, the action taken, and the newly revealed disturbance:
`t_{n+1}(h̃_n,a_n,z_{n+1}) = Φ̂(x_n,t_n(h̃_n),a_n,z_{n+1})`, with `Φ̂` measurable (Definition 5.4.5:
"for a measurable function `Φ̂`"). -/
def SuffStat.IsSequential (S : SuffStat M Pf I) (Phihat : EX → I → A → Z → I) : Prop :=
  Measurable (fun p : EX × I × A × Z => Phihat p.1 p.2.1 p.2.2.1 p.2.2.2) ∧
    ∀ n xs as zs, S.t (n + 1) xs as zs = Phihat (xs n) (S.t n xs as zs) (as n) (zs (n + 1))

end MDPFinance.BayesianModels
