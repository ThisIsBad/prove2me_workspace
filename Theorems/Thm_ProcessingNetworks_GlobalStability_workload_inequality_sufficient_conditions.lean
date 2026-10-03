import Mathlib
import Definitions.Def_ProcessingNetworks_GlobalStability_QueueingNetworkData
import Definitions.Def_ProcessingNetworks_GlobalStability_NonIdlingFluidModel
import Definitions.Def_ProcessingNetworks_GlobalStability_ReentrantLine

namespace ProcessingNetworks.GlobalStability

/-- Lemma 8.26, Dai & Harrison p. 157 (PDF p. 173), parts (a)-(d): sufficient algebraic
conditions on a positive weight vector `(x1,…,x5)` and `ε > 0` for the four workload derivative
inequalities (8.55)-(8.58) that Theorem 8.25's Lyapunov argument needs. -/
theorem workload_inequality_sufficient_conditions
    (lam1 m1 m2 m3 m4 m5 : ℝ) (hlam1 : 0 < lam1)
    (hm1 : 0 < m1) (hm2 : 0 < m2) (hm3 : 0 < m3) (hm4 : 0 < m4) (hm5 : 0 < m5)
    (Dh Fh Th Zh : ℝ → Fin 5 → ℝ)
    (hni : IsNonIdlingSolution (reentrantLineData lam1 m1 m2 m3 m4 m5) Dh Fh Th Zh) :
    (∀ x2 x4 ε : ℝ, 0 < x2 → 0 < x4 → 0 < ε →
      lam1 * (x2 + x4) + ε ≤ x2 / m2 → lam1 * (x2 + x4) + ε ≤ x4 / m4 →
      ∀ t : ℝ, 0 < t → 0 < reentrantH2 Zh t →
        ∀ d : ℝ, HasDerivAt (reentrantG2 x2 x4 Zh) d t → d ≤ -ε) ∧
    (∀ x1 x3 x5 ε : ℝ, 0 < x1 → 0 < x3 → 0 < x5 → 0 < ε →
      lam1 * (x1 + x3 + x5) + ε ≤ x1 / m1 → lam1 * (x1 + x3 + x5) + ε ≤ x3 / m3 →
      lam1 * (x1 + x3 + x5) + ε ≤ x5 / m5 →
      ∀ t : ℝ, 0 < t → 0 < reentrantH1 Zh t →
        ∀ d : ℝ, HasDerivAt (reentrantG1 x1 x3 x5 Zh) d t → d ≤ -ε) ∧
    (∀ x1 x2 x3 x4 x5 : ℝ, 0 < x1 → 0 < x2 → 0 < x3 → 0 < x4 → 0 < x5 →
      x2 + x4 ≤ x1 + x3 + x5 → x4 ≤ x3 + x5 →
      ∀ t : ℝ, 0 < t → reentrantH2 Zh t = 0 →
        reentrantG1 x1 x3 x5 Zh t ≤ reentrantG2 x2 x4 Zh t) ∧
    (∀ x1 x2 x3 x4 x5 : ℝ, 0 < x1 → 0 < x2 → 0 < x3 → 0 < x4 → 0 < x5 →
      x3 + x5 ≤ x2 + x4 → x5 ≤ x4 →
      ∀ t : ℝ, 0 < t → reentrantH1 Zh t = 0 →
        reentrantG2 x2 x4 Zh t ≤ reentrantG1 x1 x3 x5 Zh t) := by sorry

end ProcessingNetworks.GlobalStability
