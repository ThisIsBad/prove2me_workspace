import Mathlib
import Definitions.Def_PalmQueueing_Ordering_IntegralOrders
import Definitions.Def_PalmQueueing_Ordering_TimeStationary

/-!
# Lemma 4.4.2: the `S`-order compares mean cycle lengths (§4.4, p.302)
-/

namespace PalmQueueing.Ordering

open MeasureTheory

/-- **Lemma 4.4.2** (p.302). `F⁰ ≤_{S-i} F̃⁰` implies `E_{P⁰}[T] ≤ E_{P̃⁰}[T̃]`.

The `S`-orders are built by dividing Palm integrals by the mean cycle length, so it is not obvious
that they say anything about that mean itself. This lemma says they do, in the `≤_{S-i}` case: the
normalisation does not hide the comparison it normalises by.

It is the step Property 4.4.6 needs, the diagram that places the `S`-orders among the integral
orders of §4.2.1:

`≤_{I-i} ⟹ ≤_{S-i} ⟹ ≤_{S-I-i⁺}`, and `≤_{I-i} ⟹ ≤_i ⟹ ≤_{I-i⁺}`.

The proof runs through the equivalent form `F_T ≤_i F̃_T`, then (4.4.6),

`(1/E_{P⁰}[T])(1/x)∫_0^x (1 − F⁰_T(u))du ≥ (1/E_{P̃⁰}[T̃])(1/x)∫_0^x (1 − F̃⁰_T(u))du`,

and lets `x` tend to zero, using `F⁰_T(0) = F̃⁰_T(0) = 0` — which is the support restriction that
`SOrderDomain` carries, and without which the limit is a different number. -/
theorem s_order_mean {n : ℕ} (F0 F0' : Measure (Fin (n + 1) → ℝ))
    (hdom : SOrderDomain F0) (hdom' : SOrderDomain F0')
    (hle : SILe F0 F0') :
    (∫ z, z 0 ∂F0) ≤ ∫ z, z 0 ∂F0' := by sorry

end PalmQueueing.Ordering

