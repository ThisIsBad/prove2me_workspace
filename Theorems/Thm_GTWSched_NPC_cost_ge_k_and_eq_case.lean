import Mathlib
import Definitions.Def_GTWSched_NPC_Schedules

namespace GTWSched.NPC

/-- p. 336, proof of THEOREM 1: at the constructed common preferred midtime
`M = (∑ᵢ lᵢ)/2`, every schedule of `T₀, …, T₂ₙ` costs at least `k`. A schedule of cost
exactly `k` is ordered, has no gaps, has `m₀(S) = M`, and places one task of each pair on
either side of `M`. -/
theorem cost_ge_k_and_eq_case {n : ℕ} (l : Fin (2 * n + 1) → ℝ) (M : ℝ) (hl0 : 0 < l 0)
    (hmono : StrictMono l) (hM : M = (∑ i, l i) / 2)
    (s : Fin (2 * n + 1) → ℝ) (hs : IsSchedule l s) :
    kStar l ≤ commonCost l M s ∧
      (commonCost l M s = kStar l →
        Ordered l M s ∧ NoGaps l s ∧ mid l s 0 = M ∧
          ∀ i : Fin n,
            (oddTask i ∈ setA l M s ∧ evenTask i ∈ setB l M s) ∨
              (evenTask i ∈ setA l M s ∧ oddTask i ∈ setB l M s)) := by sorry

end GTWSched.NPC

