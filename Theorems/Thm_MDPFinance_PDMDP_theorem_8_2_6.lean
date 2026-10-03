import Mathlib
import Definitions.Def_MDPFinance_PDMDP_Model
import Definitions.Def_MDPFinance_PDMDP_Embedding
import Definitions.Def_MDPFinance_PDMDP_Bounding
import Definitions.Def_MDPFinance_PDMDP_Relaxed

open MeasureTheory ProbabilityTheory

namespace MDPFinance.PDMDP

variable {E U : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace U] [TopologicalSpace U] [BorelSpace U]
  [TopologicalSpace.MetrizableSpace U] [SecondCountableTopology U] [StandardBorelSpace U]

/-- Theorem 8.2.6 (Bäuerle–Rieder, p. 253, PDF 264). Suppose the Piecewise Deterministic Markov
Decision Process has a continuous upper bounding function `b` with `α_b < 1` (`c_Q c_φ < 1`, the
book's bound `α_b ≤ c_Q c_φ`) and the Continuity and Compactness Assumptions are satisfied. Then
a) `J^{rel}_∞ ∈ IM_{usc}` (in `IB_b^+` and upper semicontinuous) and `J^{rel}_∞ = T J^{rel}_∞`;
b) there exists an optimal **relaxed** stationary Markov policy `π^*_t = f(Z_n)(t-T_n)` for a
measurable decision rule `f : E → R`. `E`, `U` are Borel spaces (`U` compact by the
assumptions). -/
theorem theorem_8_2_6 (Mk : PDMDPModel E U) (EmbR : EmbeddedKernelRelaxed Mk) (b : E → ℝ)
    (hb_cont : Continuous b) (cr cQ cφ : ℝ) (hbound : IsUpperBoundingFunctionPDMDP Mk b cr cQ cφ)
    (hαb : cQ * cφ < 1) (hcc : ContinuityCompactnessAssumptions Mk b) :
    (JrelInfSup Mk EmbR ∈ IBbPlus b ∧ UpperSemicontinuous (JrelInfSup Mk EmbR) ∧
        ∀ x, JrelInfSup Mk EmbR x = Trel Mk EmbR (JrelInfSup Mk EmbR) x) ∧
      ∃ f : E → RelaxedControlFn U, Measurable f ∧
        ∀ x, JinfEmbedRelaxed Mk EmbR (fun _ => f) x = JrelInfSup Mk EmbR x := by sorry

end MDPFinance.PDMDP
