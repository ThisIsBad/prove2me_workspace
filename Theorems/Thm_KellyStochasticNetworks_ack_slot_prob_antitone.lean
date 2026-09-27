import Mathlib
import Definitions.Def_KellyStochasticNetworks_RandomAccess

namespace KellyStochasticNetworks

theorem ack_slot_prob_antitone (h : ℕ → ℝ) (hh : ∀ x, 0 ≤ h x) (t : ℕ) :
    AntitoneOn (fun ν : ℝ => ackSlotProb h ν t) (Set.Ici 0) := by sorry

end KellyStochasticNetworks
