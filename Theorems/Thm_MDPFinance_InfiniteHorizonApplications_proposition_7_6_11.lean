import Mathlib
import Definitions.Def_MDPFinance_InfiniteHorizonApplications_Bandit

open MeasureTheory ProbabilityTheory

namespace MDPFinance.InfiniteHorizonApplications

/-- Proposition 7.6.11 (Bäuerle–Rieder, p. 235, PDF 246). Let `i_0 := (m_0,n_0) \in \mathbb N_0^2`
be fixed and define `J_0(m,n) := J(m,n;I(i_0))` for `(m,n) \in \mathbb N_0^2`. Then `J_0` is the
unique solution of `v(m,n) = \max\{p(i_0)+\beta(Pv)(i_0), p(m,n)+\beta(Pv)(m,n)\}`, `(m,n) \in
\mathbb N_0^2` (unique among bounded functions, Banach's fixed point theorem in `IB_b`, `b ≡ 1`), and
it holds `I(m_0,n_0) = J_0(m_0,n_0)`. -/
theorem proposition_7_6_11 {β : ℝ} (KS : KStoppingValue β pMN) (m0 n0 : ℕ)
    (J0 : ℕ × ℕ → ℝ) (hJ0 : J0 = fun mn => KS.J (GittinsIndex KS (m0, n0)) mn) :
    ((∀ mn, J0 mn = max (pMN (m0, n0) + β * PMN J0 (m0, n0)) (pMN mn + β * PMN J0 mn)) ∧
        ∀ v : ℕ × ℕ → ℝ, (∃ C : ℝ, ∀ mn, |v mn| ≤ C) →
          (∀ mn, v mn = max (pMN (m0, n0) + β * PMN v (m0, n0)) (pMN mn + β * PMN v mn)) →
          v = J0) ∧
      GittinsIndex KS (m0, n0) = J0 (m0, n0) := by sorry

end MDPFinance.InfiniteHorizonApplications

