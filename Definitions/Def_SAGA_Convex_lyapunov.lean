import Mathlib
import Definitions.Def_SAGA_Convex_finiteSum

open scoped RealInnerProductSpace

namespace SAGA.Convex

/-- The Lyapunov function of Theorem 1 (p. 7) with the coefficient `a` of `‖x - x*‖²`:
`T(x, φ) = (1/n) ∑ᵢ fᵢ(φᵢ) - f(x*) - (1/n) ∑ᵢ ⟨f′ᵢ(x*), φᵢ - x*⟩ + a ‖x - x*‖²`.
In the proof of Theorem 2 (Appendix C, pp. 11–12) `a = c + α`. -/
noncomputable def lyapunov {d n : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (xs : EuclideanSpace ℝ (Fin d)) (a : ℝ)
    (s : EuclideanSpace ℝ (Fin d) × (Fin n → EuclideanSpace ℝ (Fin d))) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, f i (s.2 i) - fAvg f xs
    - (1 / (n : ℝ)) * ∑ i, ⟪f' i xs, s.2 i - xs⟫ + a * ‖s.1 - xs‖ ^ 2

end SAGA.Convex
