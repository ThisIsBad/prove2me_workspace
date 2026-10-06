import Mathlib
import Definitions.Def_PariMutuel_Consensus_Market

namespace PariMutuel.Consensus
theorem exists_unique_equilibrium_probabilities {m n : ℕ} (M : Market m n) :
    ∃! π : Fin n → ℝ, ∃ β : Fin m → Fin n → ℝ, M.IsEquilibrium π β := by sorry
end PariMutuel.Consensus

