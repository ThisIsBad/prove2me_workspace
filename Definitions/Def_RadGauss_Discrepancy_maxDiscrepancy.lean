import Mathlib

open MeasureTheory

namespace RadGauss.Discrepancy

/-- The half-sample difference `(2/n) Σ_{i=1}^{n/2} f(x_i) − (2/n) Σ_{i=n/2+1}^{n} f(x_i)` of a
function `f` on a sample `x = (x_1, …, x_n)` of even size `n = 2m` (Definition 2, p. 464).
Coordinates are indexed by `Fin (2 * m)`: the first half is `i.val < m`, the second half
`m ≤ i.val`. -/
noncomputable def halfDiff {X : Type*} (m : ℕ) (f : X → ℝ) (x : Fin (2 * m) → X) : ℝ :=
  (2 / ((2 * m : ℕ) : ℝ)) * ∑ i : Fin (2 * m), (if i.val < m then f (x i) else 0) -
    (2 / ((2 * m : ℕ) : ℝ)) * ∑ i : Fin (2 * m), (if i.val < m then 0 else f (x i))

/-- **Definition 2** (p. 464), the maximum discrepancy
`D̂_n(F) = sup_{f ∈ F} ((2/n) Σ_{i=1}^{n/2} f(X_i) − (2/n) Σ_{i=n/2+1}^{n} f(X_i))` of a class
`F` at a sample of even size `n = 2m`. There is no absolute value (the page uses parentheses), so
the value is a signed real. A real supremum over the subtype `F`: it is the paper's supremum when
`F` is nonempty and the family is bounded above (e.g. `F` maps into `[−1, 1]`). -/
noncomputable def empiricalMaxDiscrepancy {X : Type*} (m : ℕ) (F : Set (X → ℝ))
    (x : Fin (2 * m) → X) : ℝ :=
  ⨆ f : F, halfDiff m (f : X → ℝ) x

/-- **Definition 2** (p. 464), the expected maximum discrepancy `D_n(F) = E D̂_n(F)` for
`n = 2m`, the (Bochner) expectation over an i.i.d. sample `X_1, …, X_n` drawn from `μ`. -/
noncomputable def expectedMaxDiscrepancy {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (m : ℕ) (F : Set (X → ℝ)) : ℝ :=
  ∫ x, empiricalMaxDiscrepancy m F x ∂(Measure.pi fun _ : Fin (2 * m) => μ)

end RadGauss.Discrepancy
