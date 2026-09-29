import Mathlib
import Definitions.Def_CoresConvexGames_Stability_CoreFace

namespace CoresConvexGames.Stability

/-- Shapley (1971), p. 18, §3.1: the core configuration `{C_S}` is *regular* if `C_N ≠ O`
and `C_S ∩ C_T ⊆ C_{S ∪ T} ∩ C_{S ∩ T}` for all `S, T ⊆ N` (condition (13)). -/
def IsRegularConfiguration {n : ℕ} (f : Finset (Fin n) → ℝ) : Prop :=
  (CoreFace f Finset.univ).Nonempty ∧
    ∀ S T : Finset (Fin n),
      CoreFace f S ∩ CoreFace f T ⊆ CoreFace f (S ∪ T) ∩ CoreFace f (S ∩ T)

end CoresConvexGames.Stability
