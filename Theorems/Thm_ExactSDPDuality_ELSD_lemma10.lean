import Mathlib
import Definitions.Def_ExactSDPDuality_ELSD_Model

open Matrix

namespace ExactSDPDuality.ELSD

/-- Lemma 10 (Ramana 1997, p. 141):
(i) `𝒰ₖ` and `𝒲ₖ` are increasing set sequences;
(ii) for `k ≤ m`, `𝒲ₖ ⊆ ℳₙ` and `Q*(𝒲ₖ) ⊆ ℝᵐ` are linear subspaces;
(iii) `Q*(𝒲₁) ⊆ ⋯ ⊆ Q*(𝒲ₘ)`;
(iv) if `0 ∈ G`, then `G ⊆ (Q*(𝒲ₖ))^⊥` for every `k = 1, …, m`. -/
theorem lemma10 {n m : ℕ} (Q0 : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hQ0 : Q0.IsSymm) (hQ : ∀ i, (Q i).IsSymm) :
    (∀ k, 1 ≤ k → Uset Q0 Q k ⊆ Uset Q0 Q (k + 1) ∧ Wset Q0 Q k ⊆ Wset Q0 Q (k + 1)) ∧
      (∀ k, k ≤ m →
        (∃ S : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ),
            (S : Set (Matrix (Fin n) (Fin n) ℝ)) = Wset Q0 Q k) ∧
          ∃ S : Submodule ℝ (Fin m → ℝ), (S : Set (Fin m → ℝ)) = Qstar Q '' Wset Q0 Q k) ∧
      (∀ j k, 1 ≤ j → j ≤ k → k ≤ m → Qstar Q '' Wset Q0 Q j ⊆ Qstar Q '' Wset Q0 Q k) ∧
      ((0 : Fin m → ℝ) ∈ feasibleSet Q0 Q →
        ∀ k, 1 ≤ k → k ≤ m → feasibleSet Q0 Q ⊆ perp (Qstar Q '' Wset Q0 Q k)) := by sorry

end ExactSDPDuality.ELSD
