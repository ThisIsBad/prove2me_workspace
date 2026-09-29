import Mathlib
open Matrix

namespace PhiDivRobust.Counterpart

/-- The φ-divergence `I_φ(p, q) = ∑ᵢ qᵢ φ(pᵢ / qᵢ)` (Ben-Tal et al. 2013, p. 343, Eq. (2)), valued in
`EReal`. It is used only with `q > 0`, so the paper's conventions for `qᵢ = 0` are not needed. -/
noncomputable def phiDiv {m : ℕ} (φ : ℝ → EReal) (p q : Fin m → ℝ) : EReal :=
  ∑ i, (q i : EReal) * φ (p i / q i)

end PhiDivRobust.Counterpart
