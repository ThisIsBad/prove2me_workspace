import Mathlib

open MeasureTheory

namespace LogRegretOCO.EWOO

/-- The EWOO weight of Fig. 4 (Hazan–Agarwal–Kale 2007, p. 186):
`w_t(x) = exp(-α ∑_{τ=1}^{t-1} f_τ(x))`. Rounds are 1-based; `w_1 ≡ 1`. -/
noncomputable def ewooWeight {n : ℕ} (α : ℝ) (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (t : ℕ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.exp (-α * ∑ τ ∈ Finset.Ico 1 t, f τ x)

/-- The point played by EXPONENTIALLY WEIGHTED ONLINE OPTIMIZATION in round `t` (Fig. 4,
p. 186): the `w_t`-weighted mean of `P` under Lebesgue measure,
`x_t = (∫_P x w_t(x) dx) / (∫_P w_t(x) dx)`. -/
noncomputable def ewooPoint {n : ℕ} (P : Set (EuclideanSpace ℝ (Fin n))) (α : ℝ)
    (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (t : ℕ) : EuclideanSpace ℝ (Fin n) :=
  (∫ x in P, ewooWeight α f t x)⁻¹ • ∫ x in P, ewooWeight α f t x • x

end LogRegretOCO.EWOO
