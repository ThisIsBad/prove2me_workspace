import Mathlib
import Definitions.Def_SteinitzExchange_LocalSupermod_IntegralBaseSet
import Definitions.Def_SteinitzExchange_LocalSupermod_Matroidal

namespace SteinitzExchange.LocalSupermod

/-- Murota 1996, p. 277, Theorem 2.1. For a finite nonempty `B ⊆ ℤ^V`:
(a) (B1) ⇔ (b) `B = {x ∈ ℤ^V | x(X) ≤ f(X) ∀ X ⊆ V, x(V) = f(V)}` for an integer-valued
submodular `f` with `f(∅) = 0`; (a) ⇔ (c) the same with a supermodular `g` and `≥`.
Moreover any such `f` is `X ↦ max{x(X) | x ∈ B}` and any such `g` is `X ↦ min{x(X) | x ∈ B}`.
The page's "∀X ⊂ V" is read as all `X ⊆ V`. -/
theorem baseSet_iff_submodular_system {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hne : B.Nonempty) :
    (IsIntegralBaseSet B ↔
      ∃ f : Finset V → ℤ, IsSubmodular f ∧ f ∅ = 0 ∧
        ∀ x : V → ℤ, x ∈ B ↔
          (∀ X : Finset V, sumOn x X ≤ f X) ∧ sumOn x Finset.univ = f Finset.univ) ∧
    (IsIntegralBaseSet B ↔
      ∃ g : Finset V → ℤ, IsSupermodular g ∧ g ∅ = 0 ∧
        ∀ x : V → ℤ, x ∈ B ↔
          (∀ X : Finset V, g X ≤ sumOn x X) ∧ sumOn x Finset.univ = g Finset.univ) ∧
    (∀ f : Finset V → ℤ, IsSubmodular f → f ∅ = 0 →
      (∀ x : V → ℤ, x ∈ B ↔
          (∀ X : Finset V, sumOn x X ≤ f X) ∧ sumOn x Finset.univ = f Finset.univ) →
      ∀ X : Finset V, f X = B.sup' hne (fun x => sumOn x X)) ∧
    (∀ g : Finset V → ℤ, IsSupermodular g → g ∅ = 0 →
      (∀ x : V → ℤ, x ∈ B ↔
          (∀ X : Finset V, g X ≤ sumOn x X) ∧ sumOn x Finset.univ = g Finset.univ) →
      ∀ X : Finset V, g X = B.inf' hne (fun x => sumOn x X)) := by sorry

end SteinitzExchange.LocalSupermod

