import Mathlib
import Definitions.Def_QueueingFundamentals_GG1_Lindley

namespace QueueingFundamentals.GG1

open MeasureTheory

/-- Eqs. (6.10)–(6.12) (pp.285–286). Let `ν` be a stationary delay distribution of the G/G/1 queue
with interarrival law `A` and service law `B`, `W_q = cdfOf ν`, `U` the law of `S − T`, and
`W_q^−` as in (6.10). Then
(6.11) `W_q^−(t) + W_q(t) = ∫_{−∞}^{t} W_q(t − x) dU(x)` for all real `t`; and for every complex
`s` in the strip `0 < Re s` where `A` has the exponential moment `∫ e^{(Re s)x} dA(x) < ∞`
(a strip the page leaves implicit), `U^*(s) = A^*(−s)B^*(s)`,
`W̄_q^−(s) + W̄_q(s) = W̄_q(s)A^*(−s)B^*(s)`, and, when `A^*(−s)B^*(s) ≠ 1`,
(6.12) `W̄_q(s) = W̄_q^−(s)/(A^*(−s)B^*(s) − 1)`, with two-sided Laplace transforms `W̄`. -/
theorem wiener_hopf_transform (A B ν : Measure ℝ) (hA : IsLifetimeLaw A) (hB : IsLifetimeLaw B)
    (hν : IsStationaryDelay A B ν) :
    (∀ t : ℝ, negPart (diffLaw A B) (cdfOf ν) t + cdfOf ν t =
        ∫ x in Set.Iic t, cdfOf ν (t - x) ∂(diffLaw A B)) ∧
    ∀ s : ℂ, 0 < s.re → Integrable (fun x : ℝ => Real.exp (s.re * x)) A →
      QueueingFundamentals.MG1.lst (diffLaw A B) s = QueueingFundamentals.MG1.lst A (-s) * QueueingFundamentals.MG1.lst B s ∧
      twoSidedLaplace (negPart (diffLaw A B) (cdfOf ν)) s + twoSidedLaplace (cdfOf ν) s =
        twoSidedLaplace (cdfOf ν) s * (QueueingFundamentals.MG1.lst A (-s) * QueueingFundamentals.MG1.lst B s) ∧
      (QueueingFundamentals.MG1.lst A (-s) * QueueingFundamentals.MG1.lst B s ≠ 1 →
        twoSidedLaplace (cdfOf ν) s =
          twoSidedLaplace (negPart (diffLaw A B) (cdfOf ν)) s / (QueueingFundamentals.MG1.lst A (-s) * QueueingFundamentals.MG1.lst B s - 1)) := by sorry

end QueueingFundamentals.GG1

