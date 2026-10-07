import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace BurkholderDFI.Gundy

/-- §1, p. 20 (cited from Doob): if `f` is an `L¹`-bounded martingale or nonnegative submartingale
and `μ` is a stopping time, then `f` converges almost everywhere and `‖f_μ‖₁ ≤ ‖f‖₁`
(with `f_∞` the a.e. limit on `{μ = ∞}`). -/
theorem doob_stopped_L1 {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ P ∨ (Submartingale f ℱ P ∧ ∀ n, 1 ≤ n → 0 ≤ᵐ[P] f n))
    (hL1 : BurkholderDFI.SquareFnLp.pNorm P 1 f < ⊤) (μ : Ω → ℕ∞) (hμ : IsStoppingTime ℱ μ) :
    ∃ fInf : Ω → ℝ, (∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (fInf ω))) ∧
      ∫⁻ ω, ENNReal.ofReal |BurkholderDFI.SquareFnLp.valAt f fInf (μ ω) ω| ∂P ≤ BurkholderDFI.SquareFnLp.pNorm P 1 f := by sorry

end BurkholderDFI.Gundy

