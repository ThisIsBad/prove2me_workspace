import Mathlib
import Definitions.Def_LogRegretOCO_FTAL_IsFTLRun

namespace LogRegretOCO.FTAL
theorem ftl_regret_bound {n : ℕ} (P : Set (EuclideanSpace ℝ (Fin n))) (D R a b : ℝ)
    (g : ℕ → ℝ → ℝ) (v : ℕ → EuclideanSpace ℝ (Fin n)) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (hPne : P.Nonempty) (hPconv : Convex ℝ P) (hPclosed : IsClosed P)
    (hPbdd : Bornology.IsBounded P)
    (hdiam : ∀ y ∈ P, ∀ z ∈ P, ‖y - z‖ ≤ D)
    (hR : 0 < R) (ha : 0 < a) (hb : 0 < b)
    (hv : ∀ t, 1 ≤ t → ‖v t‖ ≤ R)
    (hgconv : ∀ t, 1 ≤ t → ConvexOn ℝ Set.univ (g t))
    (hgdiff : ∀ t, 1 ≤ t → ∀ y ∈ P, DifferentiableAt ℝ (g t) (inner ℝ (v t) y))
    (hgdiff2 : ∀ t, 1 ≤ t → ∀ y ∈ P, DifferentiableAt ℝ (deriv (g t)) (inner ℝ (v t) y))
    (hg1 : ∀ t, 1 ≤ t → ∀ y ∈ P, |deriv (g t) (inner ℝ (v t) y)| ≤ b)
    (hg2 : ∀ t, 1 ≤ t → ∀ y ∈ P, a ≤ deriv (deriv (g t)) (inner ℝ (v t) y))
    (hx : IsFTLRun P (fun t y => g t (inner ℝ (v t) y)) x) :
    ∀ T : ℕ, 1 ≤ T → ∀ u ∈ P,
      ∑ t ∈ Finset.Icc 1 T, (g t (inner ℝ (v t) (x t)) - g t (inner ℝ (v t) u))
        ≤ n * b ^ 2 / a * Real.log (a ^ 2 * D ^ 2 * R ^ 2 * T ^ 2 / b ^ 2 + 1)
          + b ^ 2 / a := by sorry
end LogRegretOCO.FTAL

