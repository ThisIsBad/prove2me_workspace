import Mathlib

namespace MaxLatticeFree.Geometry

/-- Definition 6 (Basu–Conforti–Cornuéjols–Zambelli, arXiv:1701.06543v1, p. 8).
An additive group `Λ` of `ℝⁿ` is a *lattice of the linear space* `V` if it is generated (as an
additive group, i.e. by integer combinations) by vectors `a₁, …, aₘ` that are **linearly
independent** over `ℝ` and span `V`. The family `a` is a basis of the lattice.
`ℝⁿ` is `EuclideanSpace ℝ (Fin n)`. The case `m = 0` (`Λ = {0}`, `V = {0}`) is allowed. -/
def IsLatticeOf {n : ℕ} (Λ : AddSubgroup (EuclideanSpace ℝ (Fin n)))
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∃ (m : ℕ) (a : Fin m → EuclideanSpace ℝ (Fin n)),
    LinearIndependent ℝ a ∧ Submodule.span ℝ (Set.range a) = V ∧
      Λ = AddSubgroup.closure (Set.range a)

end MaxLatticeFree.Geometry
