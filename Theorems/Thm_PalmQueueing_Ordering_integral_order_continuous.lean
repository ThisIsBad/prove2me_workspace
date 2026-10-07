import Mathlib
import Definitions.Def_PalmQueueing_Ordering_PartialOrders
import Definitions.Def_PalmQueueing_Ordering_IntegralOrders

/-!
# Lemma 4.2.1: the strong order is tested by continuous functions alone (§4.2.2, p.275)
-/

namespace PalmQueueing.Ordering

open MeasureTheory

/-- **Lemma 4.2.1** (p.275). For `F` and `G` in `𝒟(ℝ)`, `F ≤_i G` **if and only if**

`(4.2.5)  ∫_ℝ f(x)F(dx) ≤ ∫_ℝ f(x)G(dx)`

for all functions `f : ℝ → ℝ₊` which are non-decreasing **and continuous**.

The strong order is defined by testing against *all* non-decreasing functions, including the
discontinuous ones; this says the continuous ones already determine it. That reduction is what
makes the order checkable, and it is the step to Property 4.2.1 on the same page, `F ≤_i G` iff
`F̄(x) ≤ Ḡ(x)` for all `x` — the familiar tail-function criterion.

The proof is a decomposition. First, (4.2.5) for non-negative continuous non-decreasing `f` gives
it for all continuous non-decreasing `g`, via `g_n = (−n) ∨ g + n`. Then any non-negative
non-decreasing `f : ℝ → ℝ₊` is a sum `f = g + Σ_n u_n` of a continuous non-decreasing `g` and step
functions

`v_{a,b,γ}(x) = 0` for `x < a`, `γb` for `x = a`, `b` for `x > a`, with `0 ≤ γb ≤ b`,

and each such step function with `γ = 0` or `γ = 1` is a monotone limit of non-decreasing
continuous functions; a general `γ ∈ (0,1)` splits as
`v_{a,b,γ} = v_{a,γb,1} + v_{a,(1−γ)b,0}`.

Stated as an equivalence, since the forward direction is what the definition gives and the
converse is the lemma. Note that it is stated in **dimension one**: the tail criterion it leads to
has no higher-dimensional analogue, which is precisely why §4.2.3 needs Strassen. -/
theorem integral_order_continuous (F G : Measure (Fin 1 → ℝ))
    (hF : IsDistribution F) (hG : IsDistribution G) :
    StLe F G ↔
      ∀ f : (Fin 1 → ℝ) → ℝ,
        Continuous f → (∀ x, 0 ≤ f x) → (∀ x y : Fin 1 → ℝ, CoordLe x y → f x ≤ f y) →
        Integrable f F → Integrable f G →
        (∫ x, f x ∂F) ≤ ∫ x, f x ∂G := by sorry

end PalmQueueing.Ordering

