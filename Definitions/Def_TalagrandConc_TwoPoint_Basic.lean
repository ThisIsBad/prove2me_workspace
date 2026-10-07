import Mathlib
import Definitions.Def_talagrand_finite_bool_core
import Definitions.Def_TalagrandConc_OnePoint_Basic

namespace TalagrandConc.TwoPoint

open MeasureTheory
open scoped ENNReal NNReal Classical

/-- Talagrand (1995), §2.1, p. 81 and §2.3, p. 87: the product probability `P = μ^N` on
`Ω^N = {0,1}^N` (coordinates indexed by `Fin N`), where `μ({1}) = p`.
This is the published Boolean product Bernoulli measure `TalagrandCore.bernPi`. -/
noncomputable def productMeasure (N : ℕ) (p : unitInterval) : Measure (Fin N → Bool) :=
  TalagrandCore.bernPi (Fin N) (unitInterval.toNNReal p) (by
    exact_mod_cast p.property.2)

/-- Talagrand (1995), Eq. (2.1.1), p. 81: the Hamming distance from `x ∈ Ω^N` to `A ⊆ Ω^N`,
`f(A, x) = min { card {i ≤ N ; x_i ≠ y_i} ; y ∈ A }`.
It takes values in `ℝ≥0∞`; for `A = ∅` the infimum is `⊤ = +∞`. -/
noncomputable def hammingDistToSet {N : ℕ} (A : Set (Fin N → Bool)) (x : Fin N → Bool) : ℝ≥0∞ :=
  ⨅ y ∈ A, ((Finset.univ.filter (fun i => x i ≠ y i)).card : ℝ≥0∞)

/-- Talagrand (1995), Theorem 2.3.4, p. 90: the one-sided distance
`f(A, x) = min { card {i ≤ N ; x_i = 1, y_i = 0} ; y ∈ A }`, which counts only the coordinates
where `x` has a `1` and the point `y ∈ A` has a `0`.
It takes values in `ℝ≥0∞`; for `A = ∅` the infimum is `⊤ = +∞`. -/
noncomputable def oneSidedDistToSet {N : ℕ} (A : Set (Fin N → Bool)) (x : Fin N → Bool) : ℝ≥0∞ :=
  ⨅ y ∈ A, ((Finset.univ.filter (fun i => x i = true ∧ y i = false)).card : ℝ≥0∞)

/-- Talagrand (1995), Eqs. (2.3.2)–(2.3.3), p. 87: for `p ≥ 1/2`,
`b(α, t, p) = ((1 - p) e^t + p) (p + (1 - p) e^{-t/α})^α`, and for `p ≤ 1/2`,
`b(α, t, p) = ((1 - p) e^{-t} + p) (p + (1 - p) e^{t/α})^α`.
(The two formulas agree at `p = 1/2`; the second equals `b(α, t, 1 - p)` computed by the first.) -/
noncomputable def bConst (α t p : ℝ) : ℝ :=
  if 1 / 2 ≤ p then
    ((1 - p) * Real.exp t + p) * (p + (1 - p) * Real.exp (-t / α)) ^ α
  else
    ((1 - p) * Real.exp (-t) + p) * (p + (1 - p) * Real.exp (t / α)) ^ α

/-- Talagrand (1995), Theorem 2.3.4, p. 90:
`a(α, t) = max(1, (1 - p + p e^t) (p₁ e^{-t/α} + 1 - p₁)^α)`, where `p = μ({1})` and
`p₁ = μ₁({1})`. -/
noncomputable def aConst (α t p p₁ : ℝ) : ℝ :=
  max 1 ((1 - p + p * Real.exp t) * (p₁ * Real.exp (-t / α) + 1 - p₁) ^ α)

end TalagrandConc.TwoPoint
