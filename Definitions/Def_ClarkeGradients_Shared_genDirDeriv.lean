import Mathlib

open Filter Topology

namespace ClarkeGradients.Shared

/-- Clarke (1975), Definition (1.3): the *generalized directional derivative*
`f°(x; v) = limsup_{h → 0, δ ↓ 0} [f(x + h + δv) - f(x + h)] / δ`,
the `limsup` being taken along `h → 0` in `ℝⁿ` and `δ → 0⁺` jointly.
(As in the paper, this is meaningful for locally Lipschitz `f`, for which the quotient is
bounded near `(0, 0⁺)`.) -/
noncomputable def genDirDeriv {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x v : EuclideanSpace ℝ (Fin n)) : ℝ :=
  limsup (fun p : EuclideanSpace ℝ (Fin n) × ℝ => (f (x + p.1 + p.2 • v) - f (x + p.1)) / p.2)
    (𝓝 (0 : EuclideanSpace ℝ (Fin n)) ×ˢ 𝓝[>] (0 : ℝ))

end ClarkeGradients.Shared
