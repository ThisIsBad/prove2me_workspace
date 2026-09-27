import Mathlib
import Definitions.Def_Supermodularity_Games_IsSupermodularGame
import Definitions.Def_Supermodularity_Games_IsEquilibrium
import Definitions.Def_Supermodularity_Lattices_InducedSetOrder

namespace Supermodularity.Games

theorem exists_monotone_greatest_least_equilibrium {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : ι → ℕ} {T : Type*} [PartialOrder T]
    (S : T → Set (∀ i, Fin (m i) → ℝ)) (f : T → ι → (∀ i, Fin (m i) → ℝ) → ℝ)
    (hgame : ∀ t, IsSupermodularGame (S t) (f t))
    (hSne : ∀ t, (S t).Nonempty) (hScompact : ∀ t, IsCompact (S t))
    (hSinc : ∀ ⦃t t' : T⦄, t ≤ t' →
      Supermodularity.Lattices.InducedSetOrder (S t) (S t'))
    (husc : ∀ t i (x : ∀ i, Fin (m i) → ℝ),
      UpperSemicontinuousOn (fun y : Fin (m i) → ℝ => f t i (Function.update x i y))
        {y : Fin (m i) → ℝ | Function.update x i y ∈ S t})
    (hdiff : ∀ i, ∀ x ∈ (⋃ t : T, projOthers (S t) i),
      Supermodularity.Monotonicity.IncreasingDifferencesOn
        (fun (y : Fin (m i) → ℝ) (t : T) => f t i (Function.update x i y))
        ((⋃ t : T, proj (S t) i) ×ˢ (Set.univ : Set T))) :
    ∃ g l : T → (∀ i, Fin (m i) → ℝ),
      (∀ t, IsGreatest {x' : ∀ i, Fin (m i) → ℝ | IsEquilibrium (S t) (f t) x'} (g t)) ∧
      (∀ t, IsLeast {x' : ∀ i, Fin (m i) → ℝ | IsEquilibrium (S t) (f t) x'} (l t)) ∧
      Monotone g ∧ Monotone l := by sorry

end Supermodularity.Games
