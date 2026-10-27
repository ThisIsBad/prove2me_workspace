import Mathlib
import Definitions.Def_CommitOpen_Benign_Model

namespace CommitOpen.Benign

theorem sampling_negligible (α ε : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hε : 0 < ε) :
    ∃ ν : ℕ → ℝ, Negligible ν ∧
      ∀ (m : ℕ) (x xhat : Fin m → Bool),
        ∑ t ∈ Finset.univ.filter (fun t : Test m ⌊α * m⌋₊ => x ∉ goodSet ε xhat t),
          testProb m ⌊α * m⌋₊ t ≤ ν m := by sorry

end CommitOpen.Benign

