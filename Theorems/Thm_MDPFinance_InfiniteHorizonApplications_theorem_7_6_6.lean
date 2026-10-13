import Mathlib
import Definitions.Def_MDPFinance_InfiniteHorizonApplications_Bandit

open MeasureTheory ProbabilityTheory

namespace MDPFinance.InfiniteHorizonApplications

/-- Theorem 7.6.6 (Bäuerle–Rieder, p. 231, PDF 242). Let `i_0 = (m_0,n_0) \in \mathbb N_0^2` be
fixed, `r(m,n) := p(m,n)` and `(X_k)` the state process of the `K`-stopping problem started at
`i_0` under repeated pulling. Then `I(m_0,n_0) = \mathbb E_{i_0}[\sum_{k=0}^{\tau^*-1}\beta^kr(X_k)]
/((1-\beta)\mathbb E_{i_0}[\sum_{k=0}^{\tau^*-1}\beta^k]) = \sup_{\tau\ge1} \mathbb
E_{i_0}[\sum_{k=0}^{\tau-1}\beta^kr(X_k)]/((1-\beta)\mathbb E_{i_0}[\sum_{k=0}^{\tau-1}\beta^k])`
where `\tau^* := \inf\{n\in\mathbb N\mid I(X_n)\le I(i_0)\}` (`n ≥ 1`) and the supremum is over
all stopping times `τ ≥ 1`. The expectations are `EStop` (finite sums over outcome prefixes
weighted by the predictive law, discounted); `τ^*` is `tauStar`, and is asserted to be a
stopping time with `τ^* ≥ 1`. -/
theorem theorem_7_6_6 {β : ℝ} (KS : KStoppingValue β pMN) (m0 n0 : ℕ) :
    IsStoppingTime (tauStar KS (m0, n0)) ∧ IsPositiveStoppingTime (tauStar KS (m0, n0)) ∧
      GittinsIndex KS (m0, n0) =
        EStop β pMN (tauStar KS (m0, n0)) (m0, n0) /
          ((1 - β) * EStop β (fun _ => 1) (tauStar KS (m0, n0)) (m0, n0)) ∧
      GittinsIndex KS (m0, n0) =
        ⨆ τ ∈ {τ : (ℕ → ℕ × ℕ) → ℕ∞ | IsStoppingTime τ ∧ IsPositiveStoppingTime τ},
          EStop β pMN τ (m0, n0) / ((1 - β) * EStop β (fun _ => 1) τ (m0, n0)) := by sorry

end MDPFinance.InfiniteHorizonApplications

