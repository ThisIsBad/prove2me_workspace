import Mathlib
import Definitions.Def_Avram2004_Shared_scaleFun

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Avram2004.Shared

/-- The Laplace exponent (2): `ψ(θ) = log 𝔼[e^{θ X_1}]`. (Mathlib's `cgf` is `0` when `e^{θX_1}` is not
integrable, so every statement using `ψ(v)` assumes that integrability explicitly.) -/
noncomputable def psi {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ)
    (θ : ℝ) : ℝ :=
  cgf (X 1) P θ

/-- The tilted exponent (4): `ψ_c(θ) = ψ(θ + c) - ψ(c)`, the Laplace exponent of `X` under the Esscher
measure `ℙ^c`. -/
noncomputable def tilt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ)
    (c : ℝ) : ℝ → ℝ :=
  fun θ => psi P X (θ + c) - psi P X c

/-- `W_v^{(p)}`: the `p`-scale function of `(X, ℙ^v)` for every real `p` (Definition 2 for `p ≥ 0`,
the series (5) for `p < 0`). `W P X 0 q` is the untilted `W^{(q)}`. -/
noncomputable def W {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ)
    (v p : ℝ) : ℝ → ℝ :=
  scaleFunExt (tilt P X v) p

/-- `Z_v^{(p)}(x) = 1 + p ∫_{-∞}^x W_v^{(p)}(z) dz` (Definition 3 and its extension). `Z P X 0 q` is the
untilted `Z^{(q)}`. -/
noncomputable def Z {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ)
    (v p : ℝ) : ℝ → ℝ :=
  scaleZ (tilt P X v) p

end Avram2004.Shared
