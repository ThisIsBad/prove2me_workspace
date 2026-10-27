import Mathlib
import Definitions.Def_CommitOpen_Benign_Model

namespace CommitOpen.Benign

theorem corollary_4_4 {m k : ℕ} {E : Type} [Fintype E] [DecidableEq E] (ε : ℝ) (hε : 0 < ε)
    (xhat θhat θ : Fin m → Bool) (t : Test m k)
    (φt : EuclideanSpace ℂ ((Fin m → Bool) × E)) (hunit : ‖φt‖ = 1)
    (hform : ∀ y, y ∉ goodSet ε xhat t → amp θhat y φt = 0)
    (x : Fin m → Bool) (herr : relHamming t.1.2 x xhat + ε ≤ 1 / 2)
    (hpos : 0 < ∑ y ∈ agreeOn t.1.1 x, outcomeProb (mixBasis t.1.1 θhat θ) φt y) :
    maxEntropy (bobState (mixBasis t.1.1 θhat θ) φt t.1.1 x) ≤
        binEntropy2 (relHamming t.1.2 x xhat + ε) * (t.1.1ᶜ.card : ℝ) ∧
      ∀ I : Finset (Fin m), I ⊆ t.1.1ᶜ →
        0 < ∑ y ∈ agreeOn Iᶜ x, outcomeProb (mixBasis t.1.1 θhat θ) φt y →
        (hammingOn I θ θhat : ℝ) - binEntropy2 (relHamming t.1.2 x xhat + ε) * (t.1.1ᶜ.card : ℝ) ≤
          condMinEntropy (outcomeProb (mixBasis t.1.1 θhat θ) φt) I x := by sorry

end CommitOpen.Benign

