import Mathlib
import Definitions.Def_ZipkinLostSales_Bounds_Model

namespace ZipkinLostSales.Bounds

/-- Lemma 7, p. 940: the optimal cost `f_T(v)` (`fB M 1`) is nondecreasing in `v` on `V`, for the
componentwise order. -/
theorem lemma_7 {L : ℕ} (M : Data) (hM : Assumptions L M) :
    MonotoneOn (fB M 1) (ZipkinLostSales.LNatural.V L) := by sorry

end ZipkinLostSales.Bounds

