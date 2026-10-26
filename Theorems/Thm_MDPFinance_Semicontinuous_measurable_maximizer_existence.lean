import Mathlib
import Definitions.Def_MDPFinance_Semicontinuous_Model
import Definitions.Def_MDPFinance_Semicontinuous_Policy
import Definitions.Def_MDPFinance_Semicontinuous_Operators
import Definitions.Def_MDPFinance_Semicontinuous_BoundingFunction

open MeasureTheory ProbabilityTheory MDPFinance.Semicontinuous

namespace MDPFinance.Semicontinuous

/-- Proposition 2.4.11 (Bäuerle–Rieder, p. 33, PDF 48): let `v ∈ IB_b^+` and suppose (i)
`D_n(x)` is compact for all `x ∈ E`, (ii) `a ↦ L_n v(x,a)` is upper semicontinuous on `D_n(x)`
for all `x ∈ E`. Then `T_n v` is measurable and there exists a maximizer `f_n ∈ F_n` of `v`.
No topology on `D_n(·)` as a set-valued map is assumed here, unlike Proposition 2.4.3/Theorem
2.4.6 — only pointwise compactness of each fiber `D_n(x)`, which is exactly what makes this
the proposition Theorem 2.4.13 (the goal) invokes directly. `E` and `A` are Borel spaces (Borel subsets of Polish spaces with their
relative topologies: separable metrizable, with standard Borel σ-algebras), the standing assumption
of Section 2.4. -/
theorem measurable_maximizer_existence {E A : Type*}
    [MeasurableSpace E] [TopologicalSpace E] [BorelSpace E] [TopologicalSpace.MetrizableSpace E]
    [SecondCountableTopology E] [StandardBorelSpace E]
    [MeasurableSpace A] [TopologicalSpace A] [BorelSpace A] [TopologicalSpace.MetrizableSpace A]
    [SecondCountableTopology A] [StandardBorelSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (b : E → ℝ) (cr cg αb : ℝ)
    (hb : IsUpperBoundingFunction M b cr cg αb) (n : ℕ) (hn : n < N)
    (v : E → EReal) (hv : v ∈ IBbPlus b)
    (hD_compact : ∀ x, IsCompact (M.Dx n x))
    (hL_usc : ∀ x, UpperSemicontinuousOn (fun a => L M n v (x, a)) (M.Dx n x)) :
    Measurable (T M n v) ∧ ∃ f, IsMaximizer M n v f := by sorry

end MDPFinance.Semicontinuous

