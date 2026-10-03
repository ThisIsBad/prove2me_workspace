import Mathlib
import Definitions.Def_MDPFinance_Contracting_Model
import Definitions.Def_MDPFinance_Contracting_Value
import Definitions.Def_MDPFinance_Contracting_Bounding
import Definitions.Def_MDPFinance_Contracting_LsSet

open MeasureTheory ProbabilityTheory Filter Topology

namespace MDPFinance.Contracting

/-- Theorem 7.3.6 (Bäuerle–Rieder, p. 208, PDF 219), the continuous specialization of the goal.
Let `b` be a continuous bounding function and `\beta\alpha_b < 1`. If (i) `D(x)` compact,
`x \mapsto D(x)` continuous, (ii) `(x,a) \mapsto \int v(x')Q(dx'|x,a)` continuous for all
continuous `v \in IB_b`, (iii) `(x,a) \mapsto r(x,a)` continuous, then it holds: a) `J_\infty` is
continuous, `J_\infty \in IB_b` and `J_\infty = J` (Value Iteration). b) `J_\infty` is the unique
continuous fixed point of `T` in `IB_b`. c) `\emptyset \ne \mathrm{Ls}\,D_n^*(x) \subset
D_\infty^*(x)` for all `x \in E` (Policy Iteration). d) There exists `f^* \in F` with `f^*(x) \in
\mathrm{Ls}\,D_n^*(x)` for all `x \in E`, and the stationary policy `(f^*,f^*,\dots)` is
optimal. `E`, `A` Borel spaces; (ii), (iii) are conditions on `D` (with the real integral of the
real-valued `v ∈ IB_b`). -/
theorem theorem_7_3_6 {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] [TopologicalSpace E]
    [BorelSpace E] [TopologicalSpace.MetrizableSpace E] [SecondCountableTopology E]
    [StandardBorelSpace E] [TopologicalSpace A] [BorelSpace A]
    [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A] [StandardBorelSpace A]
    (M : MarkovDecisionModel E A) (b : E → ℝ) (cr αb : ℝ)
    (hb : IsBoundingFunction M b cr αb) (hbcont : Continuous b) (hαb : M.β * αb < 1)
    (hDcompact : ∀ x, IsCompact (M.Dx x)) (hDcont : ContinuousSetValued M.Dx)
    (hQcont : ∀ v ∈ IBb b, Continuous v →
      ContinuousOn (fun p : E × A => ∫ x', v x' ∂(M.Q p)) M.D)
    (hrcont : ContinuousOn M.r M.D) :
    (∃ v : E → ℝ, Continuous v ∧ v ∈ IBb b ∧ (∀ x, Jinf M x = (v x : EReal)) ∧
        ∀ x, Jinf M x = Jlim M x) ∧
      (∀ v ∈ IBb b, Continuous v → (∀ x, T' M v x = v x) → ∀ x, (v x : EReal) = Jinf M x) ∧
      (∀ x, (LsSeq fun n => Dstar M (Jn M M.r n) x).Nonempty ∧
        LsSeq (fun n => Dstar M (Jn M M.r n) x) ⊆ Dstar M (Jinf M) x) ∧
      (∃ fstar : E → A, IsDecisionRuleOf M fstar ∧
        (∀ x, fstar x ∈ LsSeq fun n => Dstar M (Jn M M.r n) x) ∧
        ∀ x, Jinfpi M M.r (fun _ => fstar) x = Jinf M x) := by sorry

end MDPFinance.Contracting
