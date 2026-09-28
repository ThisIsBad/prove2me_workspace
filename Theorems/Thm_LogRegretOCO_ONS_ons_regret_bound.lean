import Mathlib
import Definitions.Def_LogRegretOCO_ONS_Basic
import Definitions.Def_LogRegretOCO_ONS_Run

namespace LogRegretOCO.ONS

/-- Theorem 2 (Hazan–Agarwal–Kale 2007, p. 176), with the added hypothesis `n log T ≥ 4`.
Let `P ⊆ ℝⁿ` be nonempty, closed, bounded and convex with `‖x − y‖ ≤ D` on `P`; let every cost
`f_t` be differentiable on `P` with `‖∇f_t‖ ≤ G` there and `α`-exp-concave on `P`. Then every run
of the Online Newton Step with `β = ½ min{1/(4GD), α}` and `ε = 1/(β²D²)` satisfies, for every
horizon `T` with `n log T ≥ 4` and every comparator `u ∈ P`,
`Σ_{t=1}^T (f_t(x_t) − f_t(u)) ≤ 5 (1/α + GD) n log T`. -/
theorem ons_regret_bound {n : ℕ} (P : Set (EuclideanSpace ℝ (Fin n)))
    (hP_ne : P.Nonempty) (hP_closed : IsClosed P) (hP_bdd : Bornology.IsBounded P)
    (hP_conv : Convex ℝ P)
    (G D α : ℝ) (hG : 0 < G) (hD : 0 < D) (hα : 0 < α)
    (hdiam : ∀ x ∈ P, ∀ y ∈ P, ‖x - y‖ ≤ D)
    (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hdiff : ∀ t, ∀ x ∈ P, DifferentiableAt ℝ (f t) x)
    (hgrad : ∀ t, ∀ x ∈ P, ‖gradient (f t) x‖ ≤ G)
    (hexp : ∀ t, ConcaveOn ℝ P (fun x => Real.exp (-α * f t x)))
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hrun : IsONSRun P G D α f x)
    (T : ℕ) (hT : 4 ≤ (n : ℝ) * Real.log T) :
    ∀ u ∈ P, ∑ t ∈ Finset.Icc 1 T, (f t (x t) - f t u) ≤
      5 * (1 / α + G * D) * n * Real.log T := by sorry

end LogRegretOCO.ONS

