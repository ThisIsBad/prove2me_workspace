import Mathlib
import Definitions.Def_DiscreteConvex_CombinatorialC_FVal
import Definitions.Def_DiscreteConvex_CombinatorialC_NonnegOrthant
import Definitions.Def_DiscreteConvex_CombinatorialC_SubmodularOn
import Definitions.Def_DiscreteConvex_CombinatorialC_SupermodularOn
import Definitions.Def_DiscreteConvex_CombinatorialC_IsParallelArcSet
import Definitions.Def_DiscreteConvex_CombinatorialC_IsSeriesArcSet
import Definitions.Def_DiscreteConvex_CombinatorialC_ExtendOn
import Definitions.Def_DiscreteConvex_CombinatorialC_Submodular
import Definitions.Def_DiscreteConvex_CombinatorialC_Supermodular

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.83, Theorem 2.22, in
`DiscreteConvex.CombinatorialC`.
-/

namespace DiscreteConvex.CombinatorialC

/-- **Theorem 2.22.** Let `P` be a parallel arc set and `S` a series arc set. (1) `F` is
submodular in `w_P` and in `c_P`. (2) `F` is supermodular in `w_S` and in `c_S`. -/
theorem theorem_2_22_submodular_supermodular_in_parallel_series {V A : Type*} [Fintype A]
    [Fintype V] [DecidableEq V] [DecidableEq A] (src dst : A → V) (P S : Finset A)
    (hP : IsParallelArcSet src dst P) (hS : IsSeriesArcSet src dst S) (w0 c0 : A → ℝ)
    (hc0 : 0 ≤ c0) :
    (Submodular (fun wP : P → ℝ => FVal src dst (ExtendOn w0 P wP) c0) ∧
        SubmodularOn NonnegOrthant (fun cP : P → ℝ => FVal src dst w0 (ExtendOn c0 P cP))) ∧
      (Supermodular (fun wS : S → ℝ => FVal src dst (ExtendOn w0 S wS) c0) ∧
        SupermodularOn NonnegOrthant
          (fun cS : S → ℝ => FVal src dst w0 (ExtendOn c0 S cS))) := by sorry

end DiscreteConvex.CombinatorialC

