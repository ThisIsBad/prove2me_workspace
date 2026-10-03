import Mathlib
import Definitions.Def_TeschlODE_HigherDim_stableSet
import Definitions.Def_TeschlODE_HigherDim_IsInvariant

namespace TeschlODE.HigherDim

/-- Teschl, §8.1, p. 231: an invariant set `Λ` is attracting if its stable set `W⁺(Λ)` (8.8)
is a neighborhood of `Λ` (`W⁺(Λ) ∈ 𝓝ˢ Λ`, i.e. contains an open set containing `Λ`). -/
def IsAttracting {E : Type*} [NormedAddCommGroup E] (M : Set E) (I : E → Set ℝ)
    (Φ : ℝ → E → E) (Λ : Set E) : Prop :=
  IsInvariant M I Φ Λ ∧ stableSet M I Φ 1 Λ ∈ nhdsSet Λ

end TeschlODE.HigherDim
