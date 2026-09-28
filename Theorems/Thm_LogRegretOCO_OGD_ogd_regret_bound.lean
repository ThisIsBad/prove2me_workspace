import Mathlib
import Definitions.Def_LogRegretOCO_OGD_Model

namespace LogRegretOCO.OGD

/-- **Theorem 1** (p. 175): ONLINE GRADIENT DESCENT with step sizes `1/(Ht)` (the step taken
after round `t`, i.e. `η_{t+1} = 1/(Ht)` as in the proof) on `H`-strongly convex costs whose
gradients are bounded by `G` on `P` has, for every `T ≥ 1` and every comparator `u ∈ P`,
`∑_{t=1}^T (f_t(x_t) − f_t(u)) ≤ G²/(2H) · (1 + log T)`. -/
theorem ogd_regret_bound {n : ℕ} (P : Set (E n)) (hPc : Convex ℝ P) (hPcl : IsClosed P)
    (hPb : Bornology.IsBounded P) (hPne : P.Nonempty) (H G : ℝ) (hH : 0 < H) (T : ℕ)
    (hT : 1 ≤ T) (f : ℕ → E n → ℝ)
    (hsc : ∀ t ∈ Finset.Icc 1 T, IsHStrongConvex P H (f t))
    (hG : ∀ t ∈ Finset.Icc 1 T, ∀ x ∈ P, ‖gradient (f t) x‖ ≤ G)
    (η : ℕ → ℝ) (hη : ∀ t : ℕ, 1 ≤ t → η (t + 1) = 1 / (H * (t : ℝ)))
    (x : ℕ → E n) (hx : IsOGDRun P η f x) (u : E n) (hu : u ∈ P) :
    ∑ t ∈ Finset.Icc 1 T, (f t (x t) - f t u) ≤ G ^ 2 / (2 * H) * (1 + Real.log T) := by sorry

end LogRegretOCO.OGD

