import Mathlib
import Definitions.Def_ShapleyScarf_Balanced_NTUGame

namespace ShapleyScarf.Balanced

def IsBalancingWeights {N : Type*} [Fintype N] [DecidableEq N]
    (T : Finset (Finset N)) (δ : Finset N → ℝ) : Prop :=
  (∀ S, 0 ≤ δ S) ∧
  (∀ S, S ∉ T → δ S = 0) ∧
  (∀ j : N, ∑ S ∈ T, (if j ∈ S then δ S else 0) = 1)

def IsBalancedFamily {N : Type*} [Fintype N] [DecidableEq N]
    (T : Finset (Finset N)) : Prop :=
  (∀ S ∈ T, S.Nonempty) ∧ ∃ δ : Finset N → ℝ, IsBalancingWeights T δ

def IsBalancedGame {N : Type*} [Fintype N] [DecidableEq N]
    (V : Finset N → Set (N → ℝ)) : Prop :=
  IsNTUGame V ∧
  ∀ T : Finset (Finset N), IsBalancedFamily T →
    ∀ x : N → ℝ, (∀ S ∈ T, x ∈ V S) → x ∈ V Finset.univ

end ShapleyScarf.Balanced
