import Mathlib
import Definitions.Def_PalmQueueing_Palm_PointProcess

/-!
# Eq. (1.2.25): the inversion formula of Ryll-Nardzewski and Slivnyak (p.20)
-/

namespace PalmQueueing.Palm

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The inversion formula of Ryll-Nardzewski and Slivnyak**, Eq. (1.2.25) (p.20): the
`θ_t`-invariant probability is recovered from the Palm probability by averaging over one inter-point
interval,

`E[f] = λ E⁰_N [ ∫_0^{T₁} (f ∘ θ_t) dt ]`,

for **all** non-negative random variables `f` — not only bounded ones. Taking `f = 1` gives
`λ E⁰_N[T₁] = 1` (1.2.27), and `f = 1_A` gives
`P(A) = λ ∫_0^∞ P⁰_N(T₁ > t, θ_t ∈ A) dt` (1.2.26). -/
theorem inversion_formula (S : PalmSetting Ω) (f : Ω → ENNReal) (hf : Measurable f) :
    ∫⁻ ω, f ω ∂S.P
      = ENNReal.ofReal S.lam *
          ∫⁻ ω, ∫⁻ t in Set.Ioc (0 : ℝ) (S.N.T 1 ω), f (S.θ t ω) ∂(volume : Measure ℝ) ∂S.P0 := by sorry

end PalmQueueing.Palm

