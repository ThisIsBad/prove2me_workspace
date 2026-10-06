import Mathlib
import Definitions.Def_MDPFinance_Semicontinuous_Model
import Definitions.Def_MDPFinance_Semicontinuous_Policy
import Definitions.Def_MDPFinance_Semicontinuous_Operators
import Definitions.Def_MDPFinance_Semicontinuous_StructureAssumption
import Definitions.Def_MDPFinance_Semicontinuous_BoundingFunction
import Definitions.Def_MDPFinance_Semicontinuous_SetValued

open MeasureTheory ProbabilityTheory MDPFinance.Semicontinuous

namespace MDPFinance.Semicontinuous

/-- Theorem 2.4.10 (Bäuerle–Rieder, p. 33, PDF 48): suppose a Markov Decision Model with upper
bounding function `b` is given and for all `n = 0, …, N-1` it holds: (i) `D_n(x)` is compact
for all `x ∈ E` and `x ↦ D_n(x)` is continuous, (ii) `(x,a) ↦ ∫ v(x') Q_n(dx'|x,a)` is
continuous for all continuous `v ∈ IB_b^+`, (iii) `(x,a) ↦ r_n(x,a)` is continuous, (iv)
`x ↦ g_N(x)` is continuous. Then the sets `IM_n := {v ∈ IB_b^+ | v` continuous`}` and
`Δ_n := F_n` satisfy the Structure Assumption (SAN). The book's closing sentence, "if the
maximizer of `V_n` is unique, then `Δ_n` can be chosen as the set of continuous functions",
is about the value function `V_n` fixed in chunk `02a` and is not restated here — formalizing
it would require rebuilding that chunk's whole value-function/policy apparatus for a corollary
that is not this theorem's own (SAN) content; see `MODERATION_NOTES.md`. `E` and `A` are Borel spaces (Borel subsets of Polish spaces with their
relative topologies: separable metrizable, with standard Borel σ-algebras), the standing assumption
of Section 2.4. -/
theorem san_continuous {E A : Type*}
    [MeasurableSpace E] [TopologicalSpace E] [BorelSpace E] [TopologicalSpace.MetrizableSpace E]
    [SecondCountableTopology E] [StandardBorelSpace E]
    [MeasurableSpace A] [TopologicalSpace A] [BorelSpace A] [TopologicalSpace.MetrizableSpace A]
    [SecondCountableTopology A] [StandardBorelSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (b : E → ℝ) (cr cg αb : ℝ)
    (hb : IsUpperBoundingFunction M b cr cg αb)
    (hD_compact : ∀ n < N, ∀ x, IsCompact (M.Dx n x))
    (hD_cont : ∀ n < N, ContinuousSetValued (M.Dx n))
    (hQ_cont : ∀ n < N, ∀ v ∈ IBbPlus b, Continuous v →
        ContinuousOn (fun p : E × A => erealIntegral (M.Q n p) v) (M.D n))
    (hr_cont : ∀ n < N, ContinuousOn (M.r n) (M.D n))
    (hg_cont : Continuous M.g) :
    StructureAssumption M (fun _ => {v ∈ IBbPlus b | Continuous v})
      (fun n => {f | IsDecisionRule M n f}) := by sorry

end MDPFinance.Semicontinuous

