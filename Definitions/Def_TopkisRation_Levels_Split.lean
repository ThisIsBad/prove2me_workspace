import Mathlib
import Definitions.Def_TopkisRation_Levels_Model

namespace TopkisRation.Levels

variable {n : ℕ}

/-- f_t(w; z, B) of (4): the cost of interval t onward when exactly z − w units of stock are
issued in interval t, i.e. the minimum over 0 ≤ u ≤ B with 1·(B − u) = z − w of
p_t·u + g_{t−1}(w, a_t u), plus h_t(w). -/
noncomputable def Model.fw (M : Model n) (t : ℕ) (w z : ℝ) (B : Fin n → ℝ) : ℝ :=
  sInf ((fun u => M.p t ⬝ᵥ u + M.g (t - 1) w (M.a t • u)) ''
      {u | 0 ≤ u ∧ u ≤ B ∧ ∑ j, (B j - u j) = z - w}) + M.h t w

/-- u(s, B) of (5), called with s = z − w: u^j(z − w, B) = (B^{(j)} − z + w)⁺ ∧ B^j. -/
def uVec (s : ℝ) (B : Fin n → ℝ) : Fin n → ℝ :=
  fun j => min (max (tailSum B j - s) 0) (B j)

end TopkisRation.Levels
