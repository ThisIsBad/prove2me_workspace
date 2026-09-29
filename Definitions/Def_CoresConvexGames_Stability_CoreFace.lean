import Mathlib
import Definitions.Def_Supermodularity_Cooperative_Core

namespace CoresConvexGames.Stability

open Supermodularity.Cooperative

/-- Shapley (1971), p. 16, §3: the face `C_S = C ∩ H_S` of the core `C` for `O ⊂ S ⊆ N`,
where `H_S` is the hyperplane `a(S) = v(S)`; and `C_O = C` by the page's convention.
For `S = ∅` the membership condition reduces to `a ∈ C`. -/
def CoreFace {n : ℕ} (f : Finset (Fin n) → ℝ) (S : Finset (Fin n)) : Set (Fin n → ℝ) :=
  {a | a ∈ Core Finset.univ f ∧ (S.Nonempty → ∑ i ∈ S, a i = f S)}

end CoresConvexGames.Stability
