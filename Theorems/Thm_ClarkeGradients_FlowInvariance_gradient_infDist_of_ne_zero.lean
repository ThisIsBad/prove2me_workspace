import Mathlib

namespace ClarkeGradients.FlowInvariance

/-- Clarke (1975), Proposition (2.4): let `E ⊆ ℝⁿ` be nonempty and closed and
`d_E(y) = Metric.infDist y E`. If `∇d_E(x)` exists and is different from `0`, then
(1) `x ∉ E`; (2) there is a unique point `e ∈ E` closest to `x`; and
(3) `∇d_E(x) = (x - e)/|x - e|` for that point `e`. -/
theorem gradient_infDist_of_ne_zero {n : ℕ} (E : Set (EuclideanSpace ℝ (Fin n)))
    (hE : E.Nonempty) (hEc : IsClosed E) (x : EuclideanSpace ℝ (Fin n))
    (hdiff : DifferentiableAt ℝ (fun y => Metric.infDist y E) x)
    (hne : gradient (fun y => Metric.infDist y E) x ≠ 0) :
    x ∉ E ∧
      (∃! e : EuclideanSpace ℝ (Fin n), e ∈ E ∧ dist x e = Metric.infDist x E) ∧
      ∀ e ∈ E, dist x e = Metric.infDist x E →
        gradient (fun y => Metric.infDist y E) x = ‖x - e‖⁻¹ • (x - e) := by sorry

end ClarkeGradients.FlowInvariance
