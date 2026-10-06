import Mathlib
import Definitions.Def_MDPFinance_Semicontinuous_Model
import Definitions.Def_MDPFinance_Semicontinuous_Policy
import Definitions.Def_MDPFinance_Semicontinuous_Operators
import Definitions.Def_MDPFinance_Semicontinuous_BoundingFunction
import Definitions.Def_MDPFinance_Semicontinuous_SetValued

open MeasureTheory ProbabilityTheory MDPFinance.Semicontinuous

namespace MDPFinance.Semicontinuous

/-- Proposition 2.4.3 (Bäuerle–Rieder, p. 29-30, PDF 44-45): let `v ∈ IB_b^+` be upper
semicontinuous. Suppose (i) `D_n(x)` is compact for all `x ∈ E` and `x ↦ D_n(x)` is upper
semicontinuous, (ii) `(x,a) ↦ L_n v(x,a)` is upper semicontinuous on `D_n`. Then `T_n v` is
upper semicontinuous and there exists a maximizer `f_n` of `v`. `E` and `A` are Borel spaces (Borel subsets of Polish spaces with their
relative topologies: separable metrizable, with standard Borel σ-algebras), the standing assumption
of Section 2.4. -/
theorem usc_maximizer_existence {E A : Type*}
    [MeasurableSpace E] [TopologicalSpace E] [BorelSpace E] [TopologicalSpace.MetrizableSpace E]
    [SecondCountableTopology E] [StandardBorelSpace E]
    [MeasurableSpace A] [TopologicalSpace A] [BorelSpace A] [TopologicalSpace.MetrizableSpace A]
    [SecondCountableTopology A] [StandardBorelSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (b : E → ℝ) (cr cg αb : ℝ)
    (hb : IsUpperBoundingFunction M b cr cg αb) (n : ℕ) (hn : n < N)
    (v : E → EReal) (hv : v ∈ IBbPlus b) (hv_usc : UpperSemicontinuous v)
    (hD_compact : ∀ x, IsCompact (M.Dx n x)) (hD_usc : USCSetValued (M.Dx n))
    (hL_usc : UpperSemicontinuousOn (fun p : E × A => L M n v p) (M.D n)) :
    UpperSemicontinuous (T M n v) ∧ ∃ f, IsMaximizer M n v f := by sorry

end MDPFinance.Semicontinuous

