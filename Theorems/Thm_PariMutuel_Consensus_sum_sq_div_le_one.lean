import Mathlib
import Definitions.Def_PariMutuel_Consensus_Market

namespace PariMutuel.Consensus
theorem sum_sq_div_le_one {m n : ℕ} (M : Market m n) (π π' : Fin n → ℝ)
    (β β' : Fin m → Fin n → ℝ) (h : M.IsEquilibrium π β) (h' : M.IsEquilibrium π' β') :
    ∑ k, π' k * π' k / π k ≤ 1 := by sorry
end PariMutuel.Consensus

