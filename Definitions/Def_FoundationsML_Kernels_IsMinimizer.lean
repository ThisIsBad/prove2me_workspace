import Mathlib

namespace FoundationsML.Kernels

/-- `h` minimizes `F` over its whole domain: `F h ≤ F h'` for every `h'`. Formalization
scaffolding for Theorem 6.11 (Representer theorem)'s `argmin_{h∈H} F(h)`, not itself a
book-numbered definition. -/
def IsMinimizer {H α : Type*} [Preorder α] (F : H → α) (h : H) : Prop :=
  ∀ h' : H, F h ≤ F h'

end FoundationsML.Kernels
