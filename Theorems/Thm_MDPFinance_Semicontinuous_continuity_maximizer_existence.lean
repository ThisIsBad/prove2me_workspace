import Mathlib
import Definitions.Def_MDPFinance_Semicontinuous_Model
import Definitions.Def_MDPFinance_Semicontinuous_Policy
import Definitions.Def_MDPFinance_Semicontinuous_Operators
import Definitions.Def_MDPFinance_Semicontinuous_BoundingFunction
import Definitions.Def_MDPFinance_Semicontinuous_SetValued

open MeasureTheory ProbabilityTheory MDPFinance.Semicontinuous

namespace MDPFinance.Semicontinuous

/-- Proposition 2.4.8 (Bäuerle–Rieder, p. 32, PDF 47): let `v ∈ IB_b^+` be continuous. Suppose
(i) `D_n(x)` is compact for all `x ∈ E` and `x ↦ D_n(x)` is continuous, (ii)
`(x,a) ↦ L_n v(x,a)` is continuous on `D_n`. Then `T_n v` is continuous, there exists a
maximizer `f_n ∈ F_n` of `v`, and if `v` has a unique maximizer `f_n ∈ F_n` at time `n`, then
`f_n` is continuous — formalized as: any maximizer that is the *only* maximizer is
continuous. `E` and `A` are Borel spaces (Borel subsets of Polish spaces with their
relative topologies: separable metrizable, with standard Borel σ-algebras), the standing assumption
of Section 2.4. -/
theorem continuity_maximizer_existence {E A : Type*}
    [MeasurableSpace E] [TopologicalSpace E] [BorelSpace E] [TopologicalSpace.MetrizableSpace E]
    [SecondCountableTopology E] [StandardBorelSpace E]
    [MeasurableSpace A] [TopologicalSpace A] [BorelSpace A] [TopologicalSpace.MetrizableSpace A]
    [SecondCountableTopology A] [StandardBorelSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (b : E → ℝ) (cr cg αb : ℝ)
    (hb : IsUpperBoundingFunction M b cr cg αb) (n : ℕ) (hn : n < N)
    (v : E → EReal) (hv : v ∈ IBbPlus b) (hv_cont : Continuous v)
    (hD_compact : ∀ x, IsCompact (M.Dx n x)) (hD_cont : ContinuousSetValued (M.Dx n))
    (hL_cont : ContinuousOn (fun p : E × A => L M n v p) (M.D n)) :
    Continuous (T M n v) ∧ (∃ f, IsMaximizer M n v f) ∧
    (∀ f, IsMaximizer M n v f → (∀ f', IsMaximizer M n v f' → f' = f) → Continuous f) := by sorry

end MDPFinance.Semicontinuous

