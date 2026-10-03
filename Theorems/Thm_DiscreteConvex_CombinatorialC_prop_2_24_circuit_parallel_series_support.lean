import Mathlib
import Definitions.Def_DiscreteConvex_CombinatorialC_IsCircuit
import Definitions.Def_DiscreteConvex_CombinatorialC_IsParallelArcSet
import Definitions.Def_DiscreteConvex_CombinatorialC_IsSeriesArcSet
import Definitions.Def_DiscreteConvex_CombinatorialC_SuppPosR
import Definitions.Def_DiscreteConvex_CombinatorialC_SuppNegR

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.84, Proposition 2.24, in
`DiscreteConvex.CombinatorialC`.
-/

namespace DiscreteConvex.CombinatorialC

/-- **Proposition 2.24.** Let `π` be a circuit. (1) `|supp⁺(π) ∩ P| ≤ 1` and
`|supp⁻(π) ∩ P| ≤ 1` for a parallel arc set `P`. (2) `|supp⁺(π) ∩ S| = 0` or
`|supp⁻(π) ∩ S| = 0` for a series arc set `S`. -/
theorem prop_2_24_circuit_parallel_series_support {V A : Type*} [Fintype A] [Fintype V]
    [DecidableEq V] [DecidableEq A] (src dst : A → V) (pi : A → ℝ)
    (hpi : IsCircuit src dst pi) (P S : Finset A) (hP : IsParallelArcSet src dst P)
    (hS : IsSeriesArcSet src dst S) :
    ((SuppPosR pi ∩ P).card ≤ 1 ∧ (SuppNegR pi ∩ P).card ≤ 1) ∧
      ((SuppPosR pi ∩ S) = ∅ ∨ (SuppNegR pi ∩ S) = ∅) := by sorry

end DiscreteConvex.CombinatorialC
