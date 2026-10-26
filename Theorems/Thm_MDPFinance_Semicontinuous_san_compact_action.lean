import Mathlib
import Definitions.Def_MDPFinance_Semicontinuous_Model
import Definitions.Def_MDPFinance_Semicontinuous_Policy
import Definitions.Def_MDPFinance_Semicontinuous_Operators
import Definitions.Def_MDPFinance_Semicontinuous_StructureAssumption
import Definitions.Def_MDPFinance_Semicontinuous_BoundingFunction

open MeasureTheory ProbabilityTheory MDPFinance.Semicontinuous

namespace MDPFinance.Semicontinuous

/-- Theorem 2.4.13 (Bäuerle–Rieder, p. 34, PDF 49), the GOAL of this mission: suppose a Markov
Decision Model with upper bounding function `b` is given and for all `n = 0, …, N-1` it holds:
(i) `D_n(x)` is compact for all `x ∈ E`, (ii) `a ↦ ∫ v(x') Q_n(dx'|x,a)` is upper
semicontinuous for all `v ∈ IB_b^+` and for all `x ∈ E`, (iii) `a ↦ r_n(x,a)` is upper
semicontinuous for all `x ∈ E`. Then the sets `IM_n := IB_b^+` and `Δ_n := F_n` satisfy the
Structure Assumption (SAN). This is the weakest of the section's three "compactness implies
(SAN)" theorems: unlike Theorem 2.4.6 (chunk milestone `san_upper_semicontinuous`) and Theorem
2.4.10 (`san_continuous`), no continuity or semicontinuity of the set-valued map `x ↦ D_n(x)`
itself is assumed, only compactness of each fiber `D_n(x)` — and correspondingly `IM_n` is the
*whole* of `IB_b^+`, not a semicontinuous or continuous subset of it. Following the book's own
remark that this theorem "follows directly from Proposition 2.4.11" (`measurable_maximizer_
existence`), hypotheses (ii)/(iii) are stated exactly as `a ↦ ⋯` functions of the action alone,
at each fixed `x`, on the fiber `D_n(x)` — not jointly in `(x,a)` on the graph `D_n`, which
would be Theorem 2.4.6's strictly stronger hypothesis. `E` and `A` are Borel spaces (Borel subsets of Polish spaces with their
relative topologies: separable metrizable, with standard Borel σ-algebras), the standing assumption
of Section 2.4. -/
theorem san_compact_action {E A : Type*}
    [MeasurableSpace E] [TopologicalSpace E] [BorelSpace E] [TopologicalSpace.MetrizableSpace E]
    [SecondCountableTopology E] [StandardBorelSpace E]
    [MeasurableSpace A] [TopologicalSpace A] [BorelSpace A] [TopologicalSpace.MetrizableSpace A]
    [SecondCountableTopology A] [StandardBorelSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (b : E → ℝ) (cr cg αb : ℝ)
    (hb : IsUpperBoundingFunction M b cr cg αb)
    (hD_compact : ∀ n < N, ∀ x, IsCompact (M.Dx n x))
    (hQ_usc : ∀ n < N, ∀ v ∈ IBbPlus b, ∀ x,
        UpperSemicontinuousOn (fun a => erealIntegral (M.Q n (x, a)) v) (M.Dx n x))
    (hr_usc : ∀ n < N, ∀ x, UpperSemicontinuousOn (fun a => M.r n (x, a)) (M.Dx n x)) :
    StructureAssumption M (fun _ => IBbPlus b) (fun n => {f | IsDecisionRule M n f}) := by sorry

end MDPFinance.Semicontinuous

