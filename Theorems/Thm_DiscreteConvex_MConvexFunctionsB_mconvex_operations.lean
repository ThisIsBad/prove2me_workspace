import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_PosScalarMul
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_LinearWeight
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_DiscreteConvexUnivariate
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_SeparablePerturb
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_IntervalRestrict
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_Restriction


/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.143, Theorem 6.13, in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- Theorem 6.13 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.143). See the item's
`natural_language_statement` for the full statement. -/
theorem mconvex_operations {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ)
    (hf : MExchangeAxiom f) :
    (∀ lam : ℝ, 0 < lam → MExchangeAxiom (fun x => PosScalarMul lam (f x))) ∧
    (∀ a : V → ℤ, MExchangeAxiom (fun x => f (fun v => a v - x v)) ∧
      MExchangeAxiom (fun x => f (fun v => a v + x v))) ∧
    (∀ p : V → ℝ, MExchangeAxiom (LinearWeight f p)) ∧
    (∀ phi : V → ℤ → WithTop ℝ, (∀ v, DiscreteConvexUnivariate (phi v)) →
      (DomZ (SeparablePerturb f phi)).Nonempty → MExchangeAxiom (SeparablePerturb f phi)) ∧
    (∀ a b : V → WithBot (WithTop ℤ), (DomZ (IntervalRestrict f a b)).Nonempty →
      MExchangeAxiom (IntervalRestrict f a b)) ∧
    (∀ U : Finset V, (DomZ (Restriction f U)).Nonempty → MExchangeAxiom (Restriction f U)) := by sorry

end DiscreteConvex.MConvexFunctionsB
