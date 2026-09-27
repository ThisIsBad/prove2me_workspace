import Mathlib
import Definitions.Def_Supermodularity_Games_IsSupermodularGame
import Definitions.Def_Supermodularity_Games_BestJointResponse
import Definitions.Def_Supermodularity_Lattices_InducedSetOrder

namespace Supermodularity.Games

theorem bestJointResponse_compact_and_increasing {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : ι → ℕ} (S : Set (∀ i, Fin (m i) → ℝ)) (f : ι → (∀ i, Fin (m i) → ℝ) → ℝ)
    (hgame : IsSupermodularGame S f) (hSne : S.Nonempty) (hScompact : IsCompact S)
    (husc : ∀ i (x : ∀ i, Fin (m i) → ℝ),
      UpperSemicontinuousOn (fun y : Fin (m i) → ℝ => f i (Function.update x i y))
        {y : Fin (m i) → ℝ | Function.update x i y ∈ S}) :
    (∀ x ∈ S, (BestJointResponse S f x).Nonempty ∧ IsCompact (BestJointResponse S f x) ∧
      IsSublattice (BestJointResponse S f x)) ∧
    ∀ ⦃x x' : ∀ i, Fin (m i) → ℝ⦄, x ∈ S → x' ∈ S → x ≤ x' →
      Supermodularity.Lattices.InducedSetOrder (BestJointResponse S f x) (BestJointResponse S f x') := by sorry

end Supermodularity.Games
