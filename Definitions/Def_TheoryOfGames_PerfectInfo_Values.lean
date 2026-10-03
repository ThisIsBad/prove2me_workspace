import Mathlib
import Definitions.Def_TheoryOfGames_PerfectInfo_Strategy

namespace TheoryOfGames.PerfectInfo

namespace GameTree

/-- `v₁ = Max_{τ₁} Min_{τ₂} ℋ(τ₁, τ₂)` (14.4.1): the maximum over player 1's pure strategies of
the minimum over player 2's pure strategies of the normalized form. Both extrema are over
finite nonempty sets, hence attained. -/
noncomputable def v1 (t : GameTree) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun τ₁ : Strategy1 t =>
    Finset.univ.inf' Finset.univ_nonempty fun τ₂ : Strategy2 t => payoff t τ₁ τ₂

/-- `v₂ = Min_{τ₂} Max_{τ₁} ℋ(τ₁, τ₂)` (14.4.1). -/
noncomputable def v2 (t : GameTree) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty fun τ₂ : Strategy2 t =>
    Finset.univ.sup' Finset.univ_nonempty fun τ₁ : Strategy1 t => payoff t τ₁ τ₂

/-- The game is *strictly determined* (14.5.1) when `v₁ = v₂`. -/
def IsStrictlyDetermined (t : GameTree) : Prop := v1 t = v2 t

end GameTree

end TheoryOfGames.PerfectInfo
