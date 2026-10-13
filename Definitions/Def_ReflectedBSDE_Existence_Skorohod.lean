import Mathlib

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ReflectedBSDE.Existence

/-- The function `x ↦ k(x⁺)` on `ℝ`: a path `k` on `[0, ∞[` extended to the whole line by its
value at `0` on `]-∞, 0]`. -/
noncomputable def extendPath (k : ℝ≥0 → ℝ) : ℝ → ℝ := fun x => k x.toNNReal

lemma extendPath_monotone {k : ℝ≥0 → ℝ} (hk : Monotone k) : Monotone (extendPath k) :=
  fun _ _ h => hk (Real.toNNReal_le_toNNReal h)

lemma extendPath_continuous {k : ℝ≥0 → ℝ} (hk : Continuous k) : Continuous (extendPath k) :=
  hk.comp continuous_real_toNNReal

open Classical in
/-- The Lebesgue–Stieltjes measure `dk` on `ℝ` of a continuous nondecreasing path
`k : [0, ∞[ → ℝ` (extended constantly to the left of `0`, so `dk` charges no point and no part of
`]-∞, 0[`): `dk(]a, b]) = k(b) − k(a)` for `0 ≤ a ≤ b`. For a path that is not continuous and
nondecreasing the value is the zero measure; it is used only for continuous nondecreasing paths. -/
noncomputable def pathMeasure (k : ℝ≥0 → ℝ) : Measure ℝ :=
  if h : Monotone k ∧ Continuous k then
    (StieltjesFunction.mk (extendPath k) (extendPath_monotone h.1)
      (fun _ => (extendPath_continuous h.2).continuousWithinAt)).measure
  else 0

/-- Lemma 2.1 (pp. 704–705): `(y, k)` solves the Skorohod problem for the path `x` on `[0, ∞[`:
(a) `y = x + k`; (b) `y ≥ 0`; (c) `k` is continuous and nondecreasing, `k_0 = 0`, and
`∫₀^∞ y_t dk_t = 0`, the integral being taken against the Stieltjes measure `dk` of `k`. -/
def IsSkorohodSolution (x y k : ℝ≥0 → ℝ) : Prop :=
  y = x + k ∧ (∀ t, 0 ≤ y t) ∧ Continuous k ∧ Monotone k ∧ k 0 = 0 ∧
    ∫⁻ t in Ici (0 : ℝ), ENNReal.ofReal (y t.toNNReal) ∂(pathMeasure k) = 0

end ReflectedBSDE.Existence
