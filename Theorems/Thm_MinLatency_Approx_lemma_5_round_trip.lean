import Mathlib
import Definitions.Def_MinLatency_Approx_Setting

namespace MinLatency.Approx

theorem lemma_5_round_trip {V : Type} [Fintype V] [DecidableEq V]
    (d : V → V → ℝ) (p : V) (hd : IsMetric d) (α β : ℝ) (A : ℝ → List V)
    (hA : IsTSPApprox d p α β A) (σ : List V) (hσ : IsCoveringWalk p σ)
    (j J : ℕ) (hjJ : j ≤ J) :
    (Fintype.card V : ℝ) - α * ((Finset.univ.filter
          (fun v => (2 : ℝ) ^ j * nnDist d p < firstVisit d σ v)).card : ℝ)
        ≤ ((Finset.univ.filter (fun v => ∃ i ≤ j, v ∈ A (budget d p i))).card : ℝ) ∧
      ∀ v, (∃ i ≤ j, v ∈ A (budget d p i)) →
        firstVisit d (doublingWalk d p A J) v ≤ β * (2 : ℝ) ^ (j + 2) * nnDist d p := by sorry

end MinLatency.Approx

