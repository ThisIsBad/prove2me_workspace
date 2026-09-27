import Mathlib
import Definitions.Def_Supermodularity_Games_IsSupermodularGame
import Definitions.Def_Supermodularity_Games_IsEquilibrium

namespace Supermodularity.Games

theorem exists_greatest_and_least_equilibrium {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : ι → ℕ} (S : Set (∀ i, Fin (m i) → ℝ)) (f : ι → (∀ i, Fin (m i) → ℝ) → ℝ)
    (hgame : IsSupermodularGame S f) (hSne : S.Nonempty) (hScompact : IsCompact S)
    (husc : ∀ i (x : ∀ i, Fin (m i) → ℝ),
      UpperSemicontinuousOn (fun y : Fin (m i) → ℝ => f i (Function.update x i y))
        {y : Fin (m i) → ℝ | Function.update x i y ∈ S}) :
    {x' : ∀ i, Fin (m i) → ℝ | IsEquilibrium S f x'}.Nonempty ∧
    (∃ g, IsGreatest {x' : ∀ i, Fin (m i) → ℝ | IsEquilibrium S f x'} g) ∧
    (∃ l, IsLeast {x' : ∀ i, Fin (m i) → ℝ | IsEquilibrium S f x'} l) ∧
    (∀ F : Set {x' : ∀ i, Fin (m i) → ℝ // IsEquilibrium S f x'}, F.Nonempty → ∃ b, IsLUB F b) ∧
    (∀ F : Set {x' : ∀ i, Fin (m i) → ℝ // IsEquilibrium S f x'}, F.Nonempty → ∃ b, IsGLB F b) := by sorry

end Supermodularity.Games
