import Mathlib
import Definitions.Def_MDPFinance_OptimalStopping_Stationary

open MeasureTheory

namespace MDPFinance.OptimalStopping

/-- **Theorem 10.1.5** (p. 308), under (B_N). a) `J_0 = g`, `J_n = T J_{n-1}` — the value iteration
computes the value `J_n(x) = sup_{τ ≤ n} 𝔼_x[R_τ]` of the `n`-stage problem. b) `g ≤ J_n ≤ J_{n+1}`.
c) `d_{n+1}(x) = d_1(x) − β ∫ d_n^-(x') Q^X(dx'|x)`. d) `S_0^* = E`, `S_n^* = {d_n ≥ 0}`,
`S_{n+1}^* ⊂ S_n^*`; the policy `(f_N^*,…,f_1^*)` is optimal and `τ^* := min{n ∈ {0,…,N} | X_n ∈
S_{N-n}^*}` is an optimal stopping time. -/
theorem theorem_10_1_5 {E : Type*} [MeasurableSpace E] (P : StationaryProblem E) (N : ℕ)
    (Pr : E → Measure (ℕ → E)) (hPr : P.IsPathLaw Pr) (hBN : P.AssumptionBN Pr N) :
    (∀ n : ℕ, n ≤ N → ∀ x : E, P.J n x = P.valueUpTo Pr n x) ∧
    (∀ (n : ℕ) (x : E), (P.g x : EReal) ≤ P.J n x ∧ P.J n x ≤ P.J (n + 1) x) ∧
    (∀ (n : ℕ) (x : E), 1 ≤ n →
      P.d (n + 1) x = P.d 1 x - (P.beta : EReal) * erealIntegral (P.QX x) (fun y => max (-P.d n y) 0)) ∧
    (P.stopSet 0 = Set.univ ∧
      (∀ n : ℕ, 1 ≤ n → P.stopSet n = {x : E | 0 ≤ P.d n x}) ∧
      (∀ n : ℕ, P.stopSet (n + 1) ⊆ P.stopSet n) ∧
      IsStopTime (hitTimeCapped (fun n => P.stopSet (N - n)) N) ∧
      ∀ x : E, P.EReward Pr (hitTimeCapped (fun n => P.stopSet (N - n)) N) x = P.J N x) := by sorry

end MDPFinance.OptimalStopping
