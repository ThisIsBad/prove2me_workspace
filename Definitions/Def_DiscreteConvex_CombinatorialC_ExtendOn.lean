import Mathlib

/-!
Extending a vector defined on a subset `P` of arcs by a fixed background vector elsewhere,
used to view `F(w,c)` as a function of `w_P` (or `c_P`) alone (Murota, *Discrete Convex
Analysis*, SIAM 2003, p.83), in `DiscreteConvex.CombinatorialC`.
-/

namespace DiscreteConvex.CombinatorialC

/-- `ExtendOn base P vP` agrees with `vP` on `P` and with `base` outside `P`. -/
def ExtendOn {A : Type*} [DecidableEq A] (base : A → ℝ) (P : Finset A) (vP : P → ℝ) : A → ℝ :=
  fun a => if h : a ∈ P then vP ⟨a, h⟩ else base a

end DiscreteConvex.CombinatorialC
