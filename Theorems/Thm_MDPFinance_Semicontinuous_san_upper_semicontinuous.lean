import Mathlib
import Definitions.Def_MDPFinance_Semicontinuous_Model
import Definitions.Def_MDPFinance_Semicontinuous_Policy
import Definitions.Def_MDPFinance_Semicontinuous_Operators
import Definitions.Def_MDPFinance_Semicontinuous_StructureAssumption
import Definitions.Def_MDPFinance_Semicontinuous_BoundingFunction
import Definitions.Def_MDPFinance_Semicontinuous_SetValued

open MeasureTheory ProbabilityTheory MDPFinance.Semicontinuous

namespace MDPFinance.Semicontinuous

/-- Theorem 2.4.6 (Bäuerle–Rieder, p. 31, PDF 46): suppose the Markov Decision Model has an
upper bounding function `b` and for all `n = 0, …, N-1` it holds: (i) `D_n(x)` is compact for
all `x ∈ E` and `x ↦ D_n(x)` is upper semicontinuous, (ii) `(x,a) ↦ ∫ v(x') Q_n(dx'|x,a)` is
upper semicontinuous for all upper semicontinuous `v ∈ IB_b^+`, (iii) `(x,a) ↦ r_n(x,a)` is
upper semicontinuous, (iv) `x ↦ g_N(x)` is upper semicontinuous. Then the sets
`IM_n := {v ∈ IB_b^+ | v` upper semicontinuous`}` and `Δ_n := F_n` satisfy the Structure
Assumption (SAN). The book's own "in particular, `V_n ∈ IM_n` and there exists a maximizer
`f∗_n ∈ F_n` of `V_{n+1}`; the policy is optimal" is an immediate corollary of Theorem 2.3.8
(chunk `02a`) applied to this (SAN) instance, not new content of this theorem, and is not
restated here — see `MODERATION_NOTES.md`. Conditions (ii) and (iii) are required only on the
graph `D_n`, matching `r_n`'s own domain of definition there; `g_N` is total on `E`, so (iv)
carries no domain restriction. `E` and `A` are Borel spaces (Borel subsets of Polish spaces with their
relative topologies: separable metrizable, with standard Borel σ-algebras), the standing assumption
of Section 2.4. -/
theorem san_upper_semicontinuous {E A : Type*}
    [MeasurableSpace E] [TopologicalSpace E] [BorelSpace E] [TopologicalSpace.MetrizableSpace E]
    [SecondCountableTopology E] [StandardBorelSpace E]
    [MeasurableSpace A] [TopologicalSpace A] [BorelSpace A] [TopologicalSpace.MetrizableSpace A]
    [SecondCountableTopology A] [StandardBorelSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (b : E → ℝ) (cr cg αb : ℝ)
    (hb : IsUpperBoundingFunction M b cr cg αb)
    (hD_compact : ∀ n < N, ∀ x, IsCompact (M.Dx n x))
    (hD_usc : ∀ n < N, USCSetValued (M.Dx n))
    (hQ_usc : ∀ n < N, ∀ v ∈ IBbPlus b, UpperSemicontinuous v →
        UpperSemicontinuousOn (fun p : E × A => erealIntegral (M.Q n p) v) (M.D n))
    (hr_usc : ∀ n < N, UpperSemicontinuousOn (M.r n) (M.D n))
    (hg_usc : UpperSemicontinuous M.g) :
    StructureAssumption M (fun _ => {v ∈ IBbPlus b | UpperSemicontinuous v})
      (fun n => {f | IsDecisionRule M n f}) := by sorry

end MDPFinance.Semicontinuous

