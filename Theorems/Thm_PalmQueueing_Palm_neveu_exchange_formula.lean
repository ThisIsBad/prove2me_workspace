import Mathlib
import Definitions.Def_PalmQueueing_Palm_PointProcess

/-!
# Eq. (1.3.4): the Neveu exchange formula (§1.3.2, p.21)
-/

namespace PalmQueueing.Palm

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The Neveu exchange formula**, Eq. (1.3.4) (§1.3.2, p.21). Let `(N, θ_t, P)` and
`(N', θ_t, P)` be two stationary point processes with finite intensities `λ` and `λ'`, *jointly*
stationary in the sense that their stationarity is relative to the same quadruple
`(Ω, F, P, θ_t)`. Then

`λ E⁰_N[f] = λ' E⁰_{N'} [ ∫_{(0, T'₁]} (f ∘ θ_t) N(dt) ]`

for all non-negative measurable `f : (Ω, F) → (ℝ, B)`, where `T'_n` is the `n`-th point of `N'`.

The formula exchanges the roles of the two processes: it expresses an `N`-Palm expectation as an
`N'`-Palm expectation of a sum over the points of `N` in one `N'`-cycle. Its two hypotheses `hflow`
and `hprob` are what "jointly stationary" means here. -/
theorem neveu_exchange_formula (S S' : PalmSetting Ω)
    (hflow : S'.θ = S.θ) (hprob : S'.P = S.P)
    (f : Ω → ENNReal) (hf : Measurable f) :
    ENNReal.ofReal S.lam * ∫⁻ ω, f ω ∂S.P0
      = ENNReal.ofReal S'.lam *
          ∫⁻ ω, ∫⁻ t in Set.Ioc (0 : ℝ) (S'.N.T 1 ω), f (S.θ t ω) ∂(S.N.count ω) ∂S'.P0 := by sorry

end PalmQueueing.Palm

