import Mathlib
import Definitions.Def_PalmQueueing_Palm_PointProcess
import Definitions.Def_PalmQueueing_Loynes_FluidQueue

/-!
# Lemma 3.1.1: the set identity behind the fluid Little formula (§3.1.3, p.193)
-/

namespace PalmQueueing.Formulas

open MeasureTheory
open PalmQueueing.Palm PalmQueueing.Loynes

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Lemma 3.1.1** (p.193). Let `{W(t)}` be the stationary workload in a stable single server
fluid queue. For all `s < t`, the following sets are equal:

`F = { u ∈ [s,t] : W(u) > C_{u,t} }`,   `G = { u ∈ [s,t] : W(t) > A_{u,t} }`.

The left description says "the work still in the buffer at `u` exceeds everything the server could
drain between `u` and `t`"; the right says "the work in the buffer at `t` exceeds everything that
arrived since `u`". That these describe the same instants is what turns the fluid workload into an
integral over the arrival measure — Property 3.1.1 on the same page reads it off as
`W(t) = ∫_{(-∞,t]} 1_{W(s) > C_{s,t}} A(ds)` (3.1.39) — and that is the fluid analogue of Little's
formula.

Both inclusions come from the fluid-queue representation (2.7.5) of §2.7. If `u ∈ F` then
`W(t) ≥ W(u) + A_{u,t} − C_{u,t} > A_{u,t}`. Conversely if `u ∈ G` then the maximum in
`W(t) = max(W(u) + A_{u,t} − C_{u,t}, sup_{u≤v≤t}(A_{v,t} − C_{v,t}))` cannot be achieved by the
second term, since that term is bounded above by `A_{u,t}`; so
`W(u) + A_{u,t} − C_{u,t} = W(t) > A_{u,t}`.

The framework and the notation for fluid queues are those of §2.7, Chapter 2, so `IsFluidWorkload`
is imported rather than restated: `A` and `C` are the interval functions of `θ_t`-compatible
non-negative random measures (`IsFlowMeasure`, p.128), and `{W(t)}` is a `θ_t`-compatible
solution of the fluid-queue equation `(2.7.6)`. The non-negativity of `A` is load-bearing: with
`C ≡ 0`, `A_{u,t} = −(t − u)` and `W ≡ 0`, which solves `(2.7.6)`, `F` is empty while `G = [s,t)`. -/
theorem fluid_set_identity (θ : Flow Ω) (A C : ℝ → ℝ → Ω → ℝ)
    (hA : IsFlowMeasure θ A) (hC : IsFlowMeasure θ C) (W : ℝ → Ω → ℝ)
    (hWcomp : IsCompatible θ W) (hW : IsFluidWorkload A C W) (s t : ℝ) (hst : s < t) (ω : Ω) :
    {u : ℝ | u ∈ Set.Icc s t ∧ C u t ω < W u ω}
      = {u : ℝ | u ∈ Set.Icc s t ∧ A u t ω < W t ω} := by sorry

end PalmQueueing.Formulas

