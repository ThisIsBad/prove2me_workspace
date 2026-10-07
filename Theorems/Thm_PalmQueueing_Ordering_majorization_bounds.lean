import Mathlib
import Definitions.Def_PalmQueueing_Ordering_PartialOrders

/-!
# Lemma 4.1.2: the identity and the reversal bracket every reordering (§4.1.3, p.267)
-/

namespace PalmQueueing.Ordering

/-- **Lemma 4.1.2** (p.267). Let `x₁ ≤ x₂ ≤ … ≤ xₙ` and `y₁ ≤ y₂ ≤ … ≤ yₙ` be real numbers. Then,
for all `γ ∈ Γ`,

`(4.1.17)  (y − x) ≺ (y_γ − x) ≺ (y₋ − x)`,

where `y₋` is defined by `y₋ = (yₙ, …, y₁)`.

The two extremes of the majorization order over all reorderings are the **identity**, which pairs
the two sequences in the same order, and the **reversal**, which pairs them oppositely. Every
other matching lies between. Lemma 4.1.1 supplies the step; this is what iterating it gives.

This is the combinatorial heart of the FIFO optimality proof. Under a discipline `φ`, customer `k`
receives service `σ_{γ(k)}` for some permutation `γ`; FIFO is the case `γ = id`. The waiting time
vectors then satisfy `V(A', ψ) ≺ V(A, φ)` (4.1.21), and since a convex symmetric function is
Schur-convex, `E⁰[f(V_ψ)] ≤ E⁰[f(V_φ)]` for every convex `f` — Property 4.1.3.

Both inequalities of (4.1.17) are stated. The lower bound is the one Property 4.1.3 uses; the upper
says which discipline is worst. -/
theorem majorization_bounds {n : ℕ} (x y : Fin n → ℝ)
    (hx : Monotone x) (hy : Monotone y) (g : Equiv.Perm (Fin n)) :
    Majorized (fun k => y k - x k) (fun k => y (g k) - x k) ∧
    Majorized (fun k => y (g k) - x k) (fun k => reverseVec y k - x k) := by sorry

end PalmQueueing.Ordering

