import Mathlib

open scoped InnerProductSpace

namespace SAGA.StronglyConvex

/-- The Lyapunov function of Theorem 1 (p. 7) at the state `s = (x, φ)`:
`T(x, φ) = (1/n) Σ_i f_i(φ_i) - f(x*) - (1/n) Σ_i ⟨f'_i(x*), φ_i - x*⟩ + c ‖x - x*‖²`,
where `f = (1/n) Σ_i f_i`. -/
noncomputable def lyapunov {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
    (f : Fin n → E → ℝ) (f' : Fin n → E → E) (c : ℝ) (xs : E) (s : E × (Fin n → E)) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, f i (s.2 i) - (1 / (n : ℝ)) * ∑ i, f i xs
    - (1 / (n : ℝ)) * ∑ i, ⟪f' i xs, s.2 i - xs⟫_ℝ + c * ‖s.1 - xs‖ ^ 2

end SAGA.StronglyConvex
