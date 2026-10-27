import Mathlib
import Definitions.Def_MinLatency_Approx_Setting

namespace MinLatency.Approx

theorem theorem_6 :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (d : V → V → ℝ) (p : V), IsMetric d →
      ∀ O : (V → ℝ) → List V, PCAdmissible d p O →
      ∃ J : ℕ, StopsAt d p (cor4Approx d p O) J ∧
        IsCoveringWalk p (doublingWalk d p (cor4Approx d p O) J) ∧
        ∀ σ : List V, IsCoveringWalk p σ →
          walkLatency d (doublingWalk d p (cor4Approx d p O) J) ≤ 144 * walkLatency d σ) ∧
    (∃ q : Polynomial ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (d : V → V → ℚ) (p : V),
      IsMetric (fun u v => (d u v : ℝ)) →
      ∀ O : (V → ℝ) → List V, PCAdmissible (fun u v => (d u v : ℝ)) p O →
      ∃ J : ℕ, StopsAt (fun u v => (d u v : ℝ)) p (cor4Approx (fun u v => (d u v : ℝ)) p O) J ∧
        (J + 1) * Fintype.card V ≤ q.eval (instSize d) ∧
        ∀ j ≤ J, ∀ k < Fintype.card V, ∃ r : ℚ,
          (r : ℝ) = penalty (budget (fun u v => (d u v : ℝ)) p j) k ∧
          ratSize r ≤ q.eval (instSize d)) := by sorry

end MinLatency.Approx

