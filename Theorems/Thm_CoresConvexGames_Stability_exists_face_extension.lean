import Mathlib
import Definitions.Def_CoresConvexGames_Stability_CoreFace
import Definitions.Def_CoresConvexGames_Stability_IsRegularConfiguration

namespace CoresConvexGames.Stability

/-- Shapley (1971), p. 19, Lemma 2. `S ⊂⊂ N` is `S ⊂ Finset.univ ∧ S.card + 2 ≤ n`. -/
theorem exists_face_extension {n : ℕ} (f : Finset (Fin n) → ℝ) (hf0 : f ∅ = 0)
    (hreg : IsRegularConfiguration f) (S : Finset (Fin n)) (hS : S ⊂ Finset.univ)
    (hcard : S.card + 2 ≤ n) (a : Fin n → ℝ) (ha : a ∈ CoreFace f S)
    (j : Fin n) (hj : j ∉ S) :
    ∃ b ∈ CoreFace f S ∩ CoreFace f (insert j S), ∀ i ∈ S, b i = a i := by sorry

end CoresConvexGames.Stability
