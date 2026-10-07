import Mathlib
import Definitions.Def_PalmQueueing_Palm_PointProcess
import Definitions.Def_PalmQueueing_Palm_SwissArmySetting

/-!
# Theorem 1.3.1: the Swiss army formula of Palm calculus (§1.3.7, p.29)
-/

namespace PalmQueueing.Palm

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The Swiss army formula**, Theorem 1.3.1, Eq. (1.3.28) (§1.3.7, p.29). In the setting of
pp.28-29 — arrivals `{T_n}` with counting measure `A` and intensity `λ_A`, departures `{τ_n}` with
counting measure `D` and no ordering assumed, sojourn times `W_n = τ_n - T_n ≥ 0` forming a
sequence of marks of `A`, the number in system `{X(t)}` with `X(b) - X(a) = A((a,b]) - D((a,b])`, a
non-decreasing corlol integrator `{B(t)}` and a non-negative process `{Z(t)}` — for all `t`,

`λ_A E⁰_A [ ∫_{(0, W₀]} Z(s) dB(s) ]  =  (1/t) E [ ∫_{(0, t]} X(s-) Z(s) dB(s) ]`.

The book's name for it says what it is: depending on which blade is selected, this one identity
gives Little's law (`Z ≡ 1`, `B(t) = t`, whereupon it reads `λ_A E⁰_A[W₀] = E[X(0)]`), the
inversion formula, the Miyazawa conservation principle and the rate conservation law.

Two details of the statement are load-bearing. The integrator on **both** sides is `dB`, not `dA`
and not `dD`; and `X(s-)` is the left limit, not `X(s)` — the proof runs through the
Stieltjes-Lebesgue integration by parts formula (1.3.29), which needs the predictable version. -/
theorem swiss_army_formula (S : SwissArmySetting Ω) (t : ℝ) (ht : 0 < t) :
    ENNReal.ofReal S.toPalmSetting.lam *
        ∫⁻ ω, ∫⁻ s in Set.Ioc (0 : ℝ) (S.W 0 ω), ENNReal.ofReal (S.Z s ω)
          ∂((S.B.B ω).measure) ∂S.toPalmSetting.P0
      = (∫⁻ ω, ∫⁻ s in Set.Ioc (0 : ℝ) t, ENNReal.ofReal (S.Xl s ω * S.Z s ω)
          ∂((S.B.B ω).measure) ∂S.toPalmSetting.P) / ENNReal.ofReal t := by sorry

end PalmQueueing.Palm

