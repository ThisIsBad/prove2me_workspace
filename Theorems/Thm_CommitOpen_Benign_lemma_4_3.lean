import Mathlib
import Definitions.Def_CommitOpen_Benign_Model

namespace CommitOpen.Benign

theorem lemma_4_3 (α ε : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hε : 0 < ε) :
    ∃ ν : ℕ → ℝ, Negligible ν ∧
      ∀ (m : ℕ) (xhat θhat : Fin m → Bool) (E : Type) [Fintype E] [DecidableEq E]
        (φ : EuclideanSpace ℂ ((Fin m → Bool) × E)), ‖φ‖ = 1 →
        ∃ φt : Test m ⌊α * m⌋₊ → EuclideanSpace ℂ ((Fin m → Bool) × E),
          (∀ t, ‖φt t‖ = 1) ∧
          (∀ t y, y ∉ goodSet ε xhat t → amp θhat y (φt t) = 0) ∧
          traceDistance (cqState (fun _ : Test m ⌊α * m⌋₊ => φ)) (cqState φt) ≤ ν m := by sorry

end CommitOpen.Benign

