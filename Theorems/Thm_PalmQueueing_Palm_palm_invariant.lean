import Mathlib
import Definitions.Def_PalmQueueing_Palm_PointProcess

/-!
# Eq. (1.2.16): the Palm probability is invariant under the point shift (p.17)
-/

namespace PalmQueueing.Palm

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Eq. (1.2.16)** (p.17). `P⁰_N` is `θ`-invariant, where `θ` is the **point shift**
`ω ↦ θ_{T₁(ω)} ω` — the discrete shift that moves the origin to the next point, not the
continuous flow `{θ_t}` (`P` is what is invariant under that).

This is what makes `{Z(T_n)}` a stationary sequence under `P⁰_N` whenever `{Z(t)}` is compatible
with the flow, which is the form in which the rest of the book uses it. -/
theorem palm_invariant (S : PalmSetting Ω)
    (hshift : Measurable fun ω => S.θ (S.N.T 1 ω) ω) :
    Measure.map (fun ω => S.θ (S.N.T 1 ω) ω) S.P0 = S.P0 := by sorry

end PalmQueueing.Palm

