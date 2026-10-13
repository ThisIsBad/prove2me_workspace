import Mathlib
import Definitions.Def_SingleMachinePrec_Framework_CSLP

namespace SingleMachinePrec.Framework

/-- **Eqs. (6)–(8)** (p. 659). Let `P` (the precedence order of `S`) not be a linear order, let
`L_1, …, L_t` be a `k : t`-realizer of `P`, and let `x` be a half-integral optimal solution of
[CS-LP]. With `C_i = V_1 ∪ (V_{1/2} \ I_{1/2}(L_i))`:
(6) `(1/t) ∑_i w(C_i) ≤ w(V_1) + (1 - k/t) w(V_{1/2})`;
(7) `w(V_1) + (1 - k/t) w(V_{1/2}) ≤ 2 (1 - k/t) (w(V_1) + ½ w(V_{1/2}))`;
(8) `2 (1 - k/t) (w(V_1) + ½ w(V_{1/2})) ≤ (2 - 2/(t/k)) · OPT`. -/
theorem eqs_6_8 {N : Type*} [Fintype N] [DecidableEq N] (S : Instance N)
    (hP : ¬ IsLinearOrder N S.P) (k t : ℕ)
    (L : Fin t → LinearExtension S.P) (hL : IsKFoldRealizer S.P k t L)
    (x : IncPair S.P → ℝ) (hx : IsCSLPOptimal S x) (hhalf : IsHalfIntegral x) :
    (1 / (t : ℝ)) * ∑ i, weight S (roundedCover x (L i)) ≤
        weight S (levelSet x 1) + (1 - (k : ℝ) / t) * weight S (levelSet x (1 / 2)) ∧
      weight S (levelSet x 1) + (1 - (k : ℝ) / t) * weight S (levelSet x (1 / 2)) ≤
        2 * (1 - (k : ℝ) / t) *
          (weight S (levelSet x 1) + 1 / 2 * weight S (levelSet x (1 / 2))) ∧
      2 * (1 - (k : ℝ) / t) *
          (weight S (levelSet x 1) + 1 / 2 * weight S (levelSet x (1 / 2))) ≤
        (2 - 2 / ((t : ℝ) / k)) * OPT S := by sorry

end SingleMachinePrec.Framework

