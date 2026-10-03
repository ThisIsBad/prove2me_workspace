import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDuality_ConvexConjugate
import Definitions.Def_DiscreteConvex_ConjugacyDuality_Lagrange_LagrangianKernel
import Definitions.Def_DiscreteConvex_ConjugacyDuality_Lagrange_InfP
import Definitions.Def_DiscreteConvex_ConjugacyDuality_Lagrange_SupD
import Definitions.Def_DiscreteConvex_ConjugacyDuality_Lagrange_OptP
import Definitions.Def_DiscreteConvex_ConjugacyDuality_Lagrange_OptD

open DiscreteConvex.ConjugacyDuality

namespace DiscreteConvex.ConjugacyDuality.Lagrange

/-- Theorem 8.54, the saddle-point theorem (Murota, *Discrete Convex Analysis*, SIAM 2003,
p.238). Assuming the perturbation `F` is self-biconjugate in its second argument
(Eq. (8.55)): both `inf(P)` and `sup(D)` are finite and `min(P) = max(D)` if and only if there
exist `x̄ ∈ Zⱽ` and `ȳ ∈ Z^U` such that `K(x̄,ȳ)` is finite and
`K(x,ȳ) ≤ K(x̄,ȳ) ≤ K(x̄,y)` for all `x ∈ Zⱽ, y ∈ Z^U`; in this case `x̄ ∈ opt(P)` and
`ȳ ∈ opt(D)`. The page writes `min(P) = max(D)`: both values are finite **and attained**, which
is why `opt(P)` and `opt(D)` are required nonempty. Equality of a finite infimum and supremum
alone does not give a saddle point (`F(x,u) = 2^{-x} + |u|` on one coordinate each has
`inf(P) = sup(D) = 0`, attained nowhere, and no saddle point exists). -/
theorem saddle_point_theorem {V U : Type*} [Fintype U] [DecidableEq U] [Zero (U → ℤ)]
    (F : (V → ℤ) → (U → ℤ) → WithTop ℝ)
    (hF : ∀ x : V → ℤ, ConvexConjugate (ConvexConjugate (F x)) = F x) :
    ((OptP F).Nonempty ∧ (OptD F).Nonempty ∧
        InfP F ≠ ⊤ ∧ InfP F ≠ ⊥ ∧ SupD F ≠ ⊤ ∧ SupD F ≠ ⊥ ∧ InfP F = SupD F) ↔
      (∃ xbar : V → ℤ, ∃ ybar : U → ℤ,
        LagrangianKernel F xbar ybar ≠ ⊤ ∧ LagrangianKernel F xbar ybar ≠ ⊥ ∧
        (∀ x : V → ℤ, LagrangianKernel F x ybar ≤ LagrangianKernel F xbar ybar) ∧
        (∀ y : U → ℤ, LagrangianKernel F xbar ybar ≤ LagrangianKernel F xbar y) ∧
        xbar ∈ OptP F ∧ ybar ∈ OptD F) := by sorry

end DiscreteConvex.ConjugacyDuality.Lagrange
