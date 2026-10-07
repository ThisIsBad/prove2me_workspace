import Mathlib

open MeasureTheory

namespace RadGauss.RiskBound

/-- The empirical mean `Ê_n h = (1/n) Σ_{i=1}^n h(z_i)` of `h` on the sample `z = (z_1, …, z_n)`
(p. 466). -/
noncomputable def empMean {Z : Type*} {n : ℕ} (z : Fin n → Z) (h : Z → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, h (z i)

/-- The uniform deviation `sup_{h ∈ G} (E h − Ê_n h)` of a class `G` at the sample `z`
(proof of Theorem 8, p. 467), with `E h = ∫ h dP`. A real supremum over the subtype `G`;
it is a genuine supremum when `G` is nonempty and the family is bounded above. -/
noncomputable def supDev {Z : Type*} [MeasurableSpace Z] (P : Measure Z) (n : ℕ)
    (G : Set (Z → ℝ)) (z : Fin n → Z) : ℝ :=
  ⨆ h : G, ((∫ w, (h : Z → ℝ) w ∂P) - empMean z (h : Z → ℝ))

/-- The double-sample uniform deviation `sup_{h ∈ G} ((1/n) Σ_i h(z'_i) − Ê_n h)` between a ghost
sample `z'` and the sample `z` (proof of Theorem 8, p. 468, second line of the last display). -/
noncomputable def doubleSupDev {Z : Type*} (n : ℕ) (G : Set (Z → ℝ))
    (z z' : Fin n → Z) : ℝ :=
  ⨆ h : G, (empMean z' (h : Z → ℝ) - empMean z (h : Z → ℝ))

end RadGauss.RiskBound
