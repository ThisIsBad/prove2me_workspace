import Mathlib

namespace TeschlODE.Shared

/-- Teschl, §11.3, p. 296: `f : M → M` is topologically transitive if for any given (nonempty)
open sets `U, V ⊆ M` there is an `n ∈ ℕ = {1, 2, …}` such that `fⁿ(U) ∩ V ≠ ∅`. Nonemptiness of
`U` and `V` is implicit in the book (for `U = ∅` the condition fails) and explicit here. -/
def IsTopTransitive {M : Type*} [TopologicalSpace M] (f : M → M) : Prop :=
  ∀ U V : Set M, IsOpen U → IsOpen V → U.Nonempty → V.Nonempty →
    ∃ n : ℕ, 1 ≤ n ∧ (f^[n] '' U ∩ V).Nonempty

end TeschlODE.Shared
