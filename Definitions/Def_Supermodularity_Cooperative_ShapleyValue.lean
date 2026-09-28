import Mathlib

namespace Supermodularity.Cooperative

/-- `ShapleyValue f i` is the Shapley value's payoff to player `i` (Topkis p. 210):
the average, over all coalitions `S ⊆ Fin n \ {i}`, of the marginal value
`f (insert i S) - f S` of adding `i` to `S`, weighted by
`|S|! (n - |S| - 1)! / n!`. -/
noncomputable def ShapleyValue {n : ℕ} (f : Finset (Fin n) → ℝ) : Fin n → ℝ :=
  fun i => ∑ S ∈ (Finset.univ.erase i).powerset,
    (S.card.factorial * (n - S.card - 1).factorial : ℝ) / n.factorial *
      (f (insert i S) - f S)

end Supermodularity.Cooperative
