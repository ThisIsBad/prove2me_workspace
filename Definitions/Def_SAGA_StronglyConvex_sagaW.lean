import Mathlib

namespace SAGA.StronglyConvex

/-- The SAGA gradient step `w^{k+1}` of eq. (1), p. 2, from the state `(x, φ)` with index `j`:
`w = x - γ (f'_j(x) - f'_j(φ_j) + (1/n) Σ_i f'_i(φ_i))`. The table average uses the old table `φ`. -/
noncomputable def sagaW {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
    (f' : Fin n → E → E) (γ : ℝ) (x : E) (φ : Fin n → E) (j : Fin n) : E :=
  x - γ • (f' j x - f' j (φ j) + (1 / (n : ℝ)) • ∑ i, f' i (φ i))

end SAGA.StronglyConvex
