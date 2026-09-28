import Mathlib
import Definitions.Def_LogRegretOCO_ONS_Basic
import Definitions.Def_LogRegretOCO_ONS_Run

namespace LogRegretOCO.ONS

/-- §3.2, display on p. 178 (Hazan–Agarwal–Kale 2007): the regret of an Online Newton Step run is
at most `(1/(2β)) Σ_{t=1}^T ∇_tᵀ A_t⁻¹ ∇_t + 1/(2β)`, against every comparator `u ∈ P`. -/
theorem regret_le_potential {n : ℕ} (P : Set (EuclideanSpace ℝ (Fin n)))
    (hP_ne : P.Nonempty) (hP_closed : IsClosed P) (hP_bdd : Bornology.IsBounded P)
    (hP_conv : Convex ℝ P)
    (G D α : ℝ) (hG : 0 < G) (hD : 0 < D) (hα : 0 < α)
    (hdiam : ∀ x ∈ P, ∀ y ∈ P, ‖x - y‖ ≤ D)
    (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hdiff : ∀ t, ∀ x ∈ P, DifferentiableAt ℝ (f t) x)
    (hgrad : ∀ t, ∀ x ∈ P, ‖gradient (f t) x‖ ≤ G)
    (hexp : ∀ t, ConcaveOn ℝ P (fun x => Real.exp (-α * f t x)))
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hrun : IsONSRun P G D α f x) (T : ℕ) :
    ∀ u ∈ P, ∑ t ∈ Finset.Icc 1 T, (f t (x t) - f t u) ≤
      1 / (2 * onsBeta G D α) *
          ∑ t ∈ Finset.Icc 1 T, quadForm (onsMatrix G D α f x t)⁻¹ (gradient (f t) (x t)) +
        1 / (2 * onsBeta G D α) := by sorry

end LogRegretOCO.ONS

