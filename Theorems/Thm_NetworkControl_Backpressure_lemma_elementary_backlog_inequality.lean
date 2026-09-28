import Mathlib

namespace NetworkControl.Backpressure

/-- Lemma 4.3 (unnamed elementary inequality), p. 52. If `V, U, μ, A` are nonnegative reals and
`V ≤ max[U-μ,0] + A`, then `V² ≤ U² + μ² + A² - 2U(μ-A)`. A pure real-inequality lemma (no
probability, no queueing) used to bound the per-slot change in a single queue's squared backlog. -/
theorem lemma_elementary_backlog_inequality
    (V U μ A : ℝ) (hV : 0 ≤ V) (hU : 0 ≤ U) (hμ : 0 ≤ μ) (hA : 0 ≤ A)
    (h : V ≤ max (U - μ) 0 + A) :
    V ^ 2 ≤ U ^ 2 + μ ^ 2 + A ^ 2 - 2 * U * (μ - A) := by sorry

end NetworkControl.Backpressure
