import Mathlib
import Definitions.Def_CommitOpen_Benign_Model

namespace CommitOpen.Benign

theorem forces_benign (α β : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hβ : 0 < β) :
    ∃ ν : ℕ → ℝ, Negligible ν ∧
      ∀ (m : ℕ) (xhat θhat : Fin m → Bool) (E : Type) [Fintype E] [DecidableEq E]
        (φ : EuclideanSpace ℂ ((Fin m → Bool) × E)), ‖φ‖ = 1 →
        ∃ φt : Test m ⌊α * m⌋₊ → EuclideanSpace ℂ ((Fin m → Bool) × E),
          (∀ t, ‖φt t‖ = 1) ∧
          traceDistance (cqState (fun _ : Test m ⌊α * m⌋₊ => φ)) (cqState φt) ≤ ν m ∧
          ∀ (t : Test m ⌊α * m⌋₊) (θ x : Fin m → Bool),
            (∀ i ∈ t.1.2, x i = xhat i) →
            0 < ∑ y ∈ agreeOn t.1.1 x, outcomeProb (mixBasis t.1.1 θhat θ) (φt t) y →
            maxEntropy (bobState (mixBasis t.1.1 θhat θ) (φt t) t.1.1 x) ≤
                β * ((m - ⌊α * m⌋₊ : ℕ) : ℝ) ∧
              ∀ I : Finset (Fin m), I ⊆ t.1.1ᶜ →
                0 < ∑ y ∈ agreeOn Iᶜ x, outcomeProb (mixBasis t.1.1 θhat θ) (φt t) y →
                (hammingOn I θ θhat : ℝ) - β * ((m - ⌊α * m⌋₊ : ℕ) : ℝ) ≤
                  condMinEntropy (outcomeProb (mixBasis t.1.1 θhat θ) (φt t)) I x := by sorry

end CommitOpen.Benign

