import Mathlib
import Definitions.Def_Supermodularity_Lattices_InducedSetOrder
import Definitions.Def_Supermodularity_Lattices_Subcomplete

namespace Supermodularity.Lattices

theorem parametrized_fixed_point_monotone {X : Type*} [CompleteLattice X] {T : Type*}
    [PartialOrder T] (Y : X → T → Set X)
    (hne : ∀ x : X, ∀ t : T, (Y x t).Nonempty) (hsub : ∀ x : X, ∀ t : T, Subcomplete (Y x t))
    (hinc : ∀ ⦃x x' : X⦄, ∀ ⦃t t' : T⦄, x ≤ x' → t ≤ t' → InducedSetOrder (Y x t) (Y x' t')) :
    ∃ g l : T → X,
      Monotone g ∧ Monotone l ∧
        (∀ t : T, IsGreatest {x : X | x ∈ Y x t} (g t)) ∧
        (∀ t : T, IsLeast {x : X | x ∈ Y x t} (l t)) ∧
        ((∀ x' : X, ∀ ⦃t' t'' : T⦄, t' < t'' → sSup (Y x' t') < sInf (Y x' t'')) →
          StrictMono g ∧ StrictMono l) := by sorry

end Supermodularity.Lattices
