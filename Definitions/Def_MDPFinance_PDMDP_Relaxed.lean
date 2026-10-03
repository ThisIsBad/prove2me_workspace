import Mathlib
import Definitions.Def_MDPFinance_PDMDP_Model
import Definitions.Def_MDPFinance_PDMDP_Embedding

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace MDPFinance.PDMDP

variable {E U : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [MeasurableSpace U] [TopologicalSpace U]

/-- A Markov policy of the embedded model with relaxed controls: measurable `f_n : E → R`. -/
def IsRelaxedPolicy (f : ℕ → E → RelaxedControlFn U) : Prop := ∀ n, Measurable (f n)

/-- The `n`-stage reward-to-go of the embedded model **with relaxed controls** under a reward
rate `rew` (Bäuerle–Rieder, p. 250-251, PDF 261-262), in `[-∞,∞]`. -/
noncomputable def JnEmbedRelaxedWith (Mk : PDMDPModel E U) (EmbR : EmbeddedKernelRelaxed Mk)
    (rew : E × U → ℝ) (f : ℕ → E → RelaxedControlFn U) : ℕ → E → EReal
  | 0, _ => 0
  | (n + 1), x =>
      Mk.rprimeRelaxedWith rew (x, f 0 x) +
        erealIntegral (EmbR.QprimeR (x, f 0 x))
          (JnEmbedRelaxedWith Mk EmbR rew (fun k => f (k + 1)) n)

/-- `J_n(f)` of the relaxed embedded model for the reward `r`. -/
noncomputable def JnEmbedRelaxed (Mk : PDMDPModel E U) (EmbR : EmbeddedKernelRelaxed Mk)
    (f : ℕ → E → RelaxedControlFn U) : ℕ → E → EReal :=
  JnEmbedRelaxedWith Mk EmbR Mk.r f

/-- `J_∞(f)(x)` for a relaxed Markov policy, as a `limsup`. -/
noncomputable def JinfEmbedRelaxed (Mk : PDMDPModel E U) (EmbR : EmbeddedKernelRelaxed Mk)
    (f : ℕ → E → RelaxedControlFn U) (x : E) : EReal :=
  atTop.limsup fun n => JnEmbedRelaxed Mk EmbR f n x

/-- `J^{rel}_∞(x) := sup_{(f_n)} J_∞(f_n)(x)` over relaxed Markov policies (Bäuerle–Rieder,
p. 251, PDF 262). -/
noncomputable def JrelInfSup (Mk : PDMDPModel E U) (EmbR : EmbeddedKernelRelaxed Mk) (x : E) :
    EReal :=
  ⨆ f ∈ {f : ℕ → E → RelaxedControlFn U | IsRelaxedPolicy f}, JinfEmbedRelaxed Mk EmbR f x

/-- `(Lv)(x,α) := r'(x,α) + ∫ v dQ'(·|x,α)` for relaxed controls. -/
noncomputable def Lrel (Mk : PDMDPModel E U) (EmbR : EmbeddedKernelRelaxed Mk) (v : E → EReal)
    (xα : E × RelaxedControlFn U) : EReal :=
  Mk.rprimeRelaxed xα + erealIntegral (EmbR.QprimeR xα) v

/-- `(Tv)(x) := sup_{α ∈ R} (Lv)(x,α)` (Bäuerle–Rieder, p. 250, PDF 261). -/
noncomputable def Trel (Mk : PDMDPModel E U) (EmbR : EmbeddedKernelRelaxed Mk) (v : E → EReal)
    (x : E) : EReal :=
  ⨆ α : RelaxedControlFn U, Lrel Mk EmbR v (x, α)

end MDPFinance.PDMDP
