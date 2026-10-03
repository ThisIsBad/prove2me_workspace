import Mathlib
import Definitions.Def_MDPFinance_Contracting_Model
import Definitions.Def_MDPFinance_Contracting_Value

open MeasureTheory ProbabilityTheory

namespace MDPFinance.Contracting

/-- Lemma 7.1.4 (Bäuerle–Rieder, p. 197, PDF 208). For `n, m \in \mathbb N_0` with `n \ge m` it
holds: a) `J_n^\pi \le J_m^\pi + T^m_\circ \delta` for `π ∈ F^∞`. b) `J_n \le J_m + T^m_\circ \delta`. -/
theorem lemma_7_1_4 {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] (M : MarkovDecisionModel E A)
    (π : ℕ → E → A) (hπ : IsPolicyOf M π) (n m : ℕ) (hnm : m ≤ n) (x : E) :
    Jnpi M M.r π n x ≤ Jnpi M M.r π m x + (Tcirc M)^[m] (delta M) x ∧
      Jn M M.r n x ≤ Jn M M.r m x + (Tcirc M)^[m] (delta M) x := by sorry

end MDPFinance.Contracting
