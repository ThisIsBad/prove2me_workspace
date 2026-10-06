import Mathlib
import Definitions.Def_MDPFinance_Semicontinuous_Model
import Definitions.Def_MDPFinance_Semicontinuous_Operators
import Definitions.Def_MDPFinance_Semicontinuous_BoundingFunction

open MeasureTheory ProbabilityTheory MDPFinance.Semicontinuous

namespace MDPFinance.Semicontinuous

/-- Lemma 2.4.7 (Bäuerle–Rieder, p. 31, PDF 46): let `b` be a continuous upper bounding
function. Then the following are equivalent, for an arbitrary stochastic kernel `Q` on `E`
given `E × A`: (i) `(x,a) ↦ ∫ v(x') Q(dx'|x,a)` is upper semicontinuous for all upper
semicontinuous `v ∈ IB_b^+`; (ii) `(x,a) ↦ ∫ b(x') Q(dx'|x,a)` is continuous, and
`(x,a) ↦ ∫ v(x') Q(dx'|x,a)` is continuous and bounded for all continuous and bounded `v` on
`E`. A kernel satisfying (ii) is called weakly continuous. `b`'s role as an upper bounding
function of the ambient model `M` is carried only as standing context (the section's own
running hypothesis); the equivalence itself concerns an arbitrary stochastic kernel `Q`, not necessarily
one of `M`'s own `Q_n`, exactly as the book states it, under which `b` is integrable (`hQb`, as it is
under each `Q_n` by Definition 2.4.1(iii)), so that `∫ b dQ` in (ii) is the genuine integral. `E` and `A` are Borel spaces (Borel subsets of Polish spaces with their
relative topologies: separable metrizable, with standard Borel σ-algebras), the standing assumption
of Section 2.4. -/
theorem weakly_continuous_kernel_iff {E A : Type*}
    [MeasurableSpace E] [TopologicalSpace E] [BorelSpace E] [TopologicalSpace.MetrizableSpace E]
    [SecondCountableTopology E] [StandardBorelSpace E]
    [MeasurableSpace A] [TopologicalSpace A] [BorelSpace A] [TopologicalSpace.MetrizableSpace A]
    [SecondCountableTopology A] [StandardBorelSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (b : E → ℝ) (cr cg αb : ℝ)
    (hb : IsUpperBoundingFunction M b cr cg αb) (hb_cont : Continuous b)
    (Q : Kernel (E × A) E) [∀ p, IsProbabilityMeasure (Q p)]
    (hQb : ∀ p, ∫⁻ x', ENNReal.ofReal (b x') ∂(Q p) < ⊤) :
    (∀ v : E → EReal, v ∈ IBbPlus b → UpperSemicontinuous v →
        UpperSemicontinuous (fun p : E × A => erealIntegral (Q p) v))
    ↔
    (Continuous (fun p : E × A => ∫ x', b x' ∂(Q p)) ∧
     ∀ v : E → ℝ, Continuous v → (∃ c, ∀ x, |v x| ≤ c) →
       Continuous (fun p : E × A => ∫ x', v x' ∂(Q p)) ∧
       ∃ c, ∀ p, |∫ x', v x' ∂(Q p)| ≤ c) := by sorry

end MDPFinance.Semicontinuous

