import Mathlib

namespace TeschlQM.KatoRellich

open scoped ENNReal

/-- The operator norm `‖T‖ = sup_{φ ∈ 𝔇(T), φ ≠ 0} ‖Tφ‖ / ‖φ‖ ∈ [0, ∞]` of a linear operator
`T : 𝔇(T) → ℌ`. It is finite exactly when `T` is bounded on its domain; the value `∞` stands for an
unbounded `T` (never a junk `0`). The term `φ = 0` contributes `0 / 0 = 0`. -/
noncomputable def opNorm {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →ₗ.[ℂ] H) : ℝ≥0∞ :=
  ⨆ φ : T.domain, (‖T φ‖₊ : ℝ≥0∞) / (‖(φ : H)‖₊ : ℝ≥0∞)

end TeschlQM.KatoRellich
