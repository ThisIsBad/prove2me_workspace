import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_MooreLateJobs_NumLate_lateSet
import Definitions.Def_LawlerMoore_WeightedTardy_weightedTardy
import Definitions.Def_LawlerMoore_WeightedTardy_eq3

namespace LawlerMoore.WeightedTardy

open MooreLateJobs.Shared

/-- §§5–6 and Eq. (3) (pp. 79–80): with the jobs numbered by deadline (`d` monotone) and
penalties `p j ≥ 0`, the value `f(n, d_n)` of Equation (3) is finite, `f(n, d_n) = V`, and the
minimum over all sequences of the weighted number of tardy jobs is `∑_j p_j - V`. -/
theorem min_weighted_tardy_eq {n : ℕ} (hn : 0 < n) (a' d : Fin n → ℕ) (p : Fin n → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hd : Monotone d) :
    ∃ V : ℝ, eq3 a' d p n (d ⟨n - 1, by omega⟩ : ℤ) = (V : WithBot ℝ) ∧
      IsLeast {w : ℝ | ∃ l : List (Fin n), IsSchedule Finset.univ l ∧ w = weightedTardy a' d p l}
        ((∑ j, p j) - V) := by sorry

end LawlerMoore.WeightedTardy

