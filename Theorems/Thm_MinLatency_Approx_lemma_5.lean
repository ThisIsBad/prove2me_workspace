import Mathlib
import Definitions.Def_MinLatency_Approx_Setting

namespace MinLatency.Approx

theorem lemma_5 :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (d : V → V → ℝ) (p : V), IsMetric d →
      ∀ (α β : ℝ) (A : ℝ → List V), IsTSPApprox d p α β A →
      ∃ J : ℕ, StopsAt d p A J ∧ IsCoveringWalk p (doublingWalk d p A J) ∧
        ∀ σ : List V, IsCoveringWalk p σ →
          walkLatency d (doublingWalk d p A J) ≤
            8 * ((⌈α⌉ : ℤ) : ℝ) * β * walkLatency d σ) ∧
    (∃ q : Polynomial ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (d : V → V → ℚ) (p : V),
      IsMetric (fun u v => (d u v : ℝ)) →
      ∀ (α β : ℝ) (A : ℝ → List V), IsTSPApprox (fun u v => (d u v : ℝ)) p α β A →
      ∃ J : ℕ, StopsAt (fun u v => (d u v : ℝ)) p A J ∧ J + 1 ≤ q.eval (instSize d)) := by sorry

end MinLatency.Approx

