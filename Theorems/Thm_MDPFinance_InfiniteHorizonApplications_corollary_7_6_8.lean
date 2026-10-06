import Mathlib
import Definitions.Def_MDPFinance_InfiniteHorizonApplications_Bandit

open MeasureTheory ProbabilityTheory

namespace MDPFinance.InfiniteHorizonApplications

/-- Corollary 7.6.8 (Bäuerle–Rieder, p. 232, PDF 243). The Gittins-indices have the following
properties: a) The optimal stopping set for the `K`-stopping problem is `\{(m,n) \mid J(m,n;K) =
K\} = \{(m,n) \mid I(m,n) \le K\}`. b) The indifference property: `I(m,n) = J(m,n;I(m,n)) =
p(m,n) + \beta(PJ)(m,n;I(m,n))`. c) `p(m,n)/(1-\beta) \le I(m,n) \le 1/(1-\beta)`. d) If the
success probability is known — the `K`-stopping problem of an arm with constant success
probability `p_0`, `KStoppingValue β (fun _ => p_0)` — then `I(m,n) = p_0/(1-\beta)` (the draft's
rendering `∀ m n, p(m,n) = p_0` is false for the Beta-Bernoulli `p`, making the clause vacuous). -/
theorem corollary_7_6_8 {β : ℝ} (KS : KStoppingValue β pMN) :
    (∀ K m n, KS.J K (m, n) = K ↔ GittinsIndex KS (m, n) ≤ K) ∧
      (∀ m n, GittinsIndex KS (m, n) = KS.J (GittinsIndex KS (m, n)) (m, n) ∧
        GittinsIndex KS (m, n) =
          pMN (m, n) + β * PMN (KS.J (GittinsIndex KS (m, n))) (m, n)) ∧
      (∀ m n, pMN (m, n) / (1 - β) ≤ GittinsIndex KS (m, n) ∧
        GittinsIndex KS (m, n) ≤ 1 / (1 - β)) ∧
      (∀ p0 : ℝ, ∀ KS' : KStoppingValue β (fun _ => p0), ∀ m n,
        GittinsIndex KS' (m, n) = p0 / (1 - β)) := by sorry

end MDPFinance.InfiniteHorizonApplications

