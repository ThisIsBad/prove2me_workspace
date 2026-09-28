import Mathlib
import Definitions.Def_CubicNewton_Shared_lamMin

namespace CubicNewton.LocalQuad

/-- The quantity `δ = L‖f′(x)‖ / λₙ²(f″(x))` of Nesterov–Polyak 2006, Section 3, p. 186 (defined
there for the iterates, `δ_k = L‖f′(x_k)‖ / λₙ²(f″(x_k))`), with `g x` for `f′(x)`, `H x` for
`f″(x)` and `lamMin` for `λₙ`. The paper uses it only where `f″(x) ≻ 0`, i.e. `0 < lamMin (H x)`;
when `lamMin (H x) = 0` Lean's division returns `0`. -/
noncomputable def deltaMeasure {n : ℕ} (L : ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  L * ‖g x‖ / CubicNewton.Shared.lamMin (H x) ^ 2

end CubicNewton.LocalQuad
