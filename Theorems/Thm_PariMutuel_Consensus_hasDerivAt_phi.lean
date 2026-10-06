import Mathlib
import Definitions.Def_PariMutuel_Consensus_Market
import Definitions.Def_PariMutuel_Consensus_Phi

namespace PariMutuel.Consensus
theorem hasDerivAt_phi {m n : ℕ} (M : Market m n) (ξ : Fin m → Fin n → ℝ)
    (hξ : ∀ i, 0 < ∑ j, M.P i j * ξ i j) (i : Fin m) (j : Fin n) :
    HasDerivAt (fun t : ℝ => M.phi (Function.update ξ i (Function.update (ξ i) j t)))
      (M.b i * M.P i j / ∑ s, M.P i s * ξ i s) (ξ i j) := by sorry
end PariMutuel.Consensus

