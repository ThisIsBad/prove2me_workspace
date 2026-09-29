import Mathlib
import Definitions.Def_Supermodularity_Lattices_InducedSetOrder
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn
import Definitions.Def_Supermodularity_Matching_IsOptimalMatching
import Definitions.Def_Supermodularity_Matching_IsIncreasingMatching

namespace Supermodularity.Matching

theorem argmax_increasing_and_matching_exists_of_loose
    {n m : ℕ} {X : Fin n → Type*} [∀ i, Lattice (X i)] [∀ i, Fintype (X i)]
    [∀ i, Nonempty (X i)]
    (f : (∀ i, X i) → Fin m → ℝ)
    (hf : Supermodularity.Monotonicity.SupermodularOn
      (fun p : (∀ i, X i) × Fin m => f p.1 p.2) Set.univ)
    (hloose : ∀ x : Fin m → ∀ i, X i,
        IsOptimalMatching f x ↔ ∀ j : Fin m, ∀ y : ∀ i, X i, f y j ≤ f (x j) j) :
    (∀ ⦃j k : Fin m⦄, j ≤ k →
        Supermodularity.Lattices.InducedSetOrder
          {x : ∀ i, X i | ∀ y : ∀ i, X i, f y j ≤ f x j}
          {x : ∀ i, X i | ∀ y : ∀ i, X i, f y k ≤ f x k}) ∧
      ∃ x : Fin m → ∀ i, X i, IsIncreasingMatching x ∧ IsOptimalMatching f x := by sorry

end Supermodularity.Matching
