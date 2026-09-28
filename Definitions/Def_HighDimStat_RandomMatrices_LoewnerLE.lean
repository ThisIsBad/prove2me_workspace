import Mathlib

namespace HighDimStat.RandomMatrices

/-- The **Loewner (positive semidefinite) order** `A ⪯ B` on symmetric matrices, used throughout
Wainwright, *High-Dimensional Statistics* (2019), Section 6.4.1, to state matrix tail conditions
(Eqs. (6.27)-(6.31)): `A ⪯ B` iff `B - A` is positive semidefinite. -/
def LoewnerLE {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  (B - A).PosSemidef

end HighDimStat.RandomMatrices
