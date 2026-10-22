import Mathlib
import Definitions.Def_FracPackCover_Covering_Basic
import Definitions.Def_FracPackCover_Covering_ImproveCover

namespace FracPackCover.Covering

/-- Lemma 3.4 (Plotkin–Shmoys–Tardos, Cornell ORIE TR 999, p. 19). Let `0 < ε < 1` and let
IMPROVE-COVER(x, ε) (Figure 3) start from `x ∈ P` with `λ0 = λ(x) > 0`, width bound `ρ` and an
exact maximization oracle. Then every point `(x_t, λ_t)` reached during its execution has
`λ_t ≥ 3λ0/4`. -/
theorem lemma_3_4 {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (P : Set (Fin n → ℝ)) (hdata : IsCoveringData A b P) (ρ : ℝ) (hρ : WidthBound A b P ρ)
    (orc : (Fin m → ℝ) → (Fin n → ℝ)) (horc : IsMaxOracle A P orc)
    (x : Fin n → ℝ) (hx : x ∈ P) (hlam : 0 < lam A b x) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (t : ℕ) (ht : IsReachedCover A b orc ρ ε x t) :
    3 * lam A b x / 4 ≤ lam A b (coverIterate A b orc ρ ε x t) := by sorry

end FracPackCover.Covering

