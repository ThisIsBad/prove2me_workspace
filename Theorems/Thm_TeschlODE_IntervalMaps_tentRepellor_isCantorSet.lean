import Mathlib
import Definitions.Def_TeschlODE_Shared_tentRepellor
import Definitions.Def_TeschlODE_IntervalMaps_IsCantorSet

namespace TeschlODE.IntervalMaps

/-- Teschl, Lemma 11.4, p. 299: for the tent map `T_µ` with `µ > 2` (the standing assumption of
§11.4), the set `Λ` (11.18) of points staying in `[0, 1]` under all iterations is a Cantor set:
compact, totally disconnected and perfect. -/
theorem tentRepellor_isCantorSet (μ : ℝ) (hμ : 2 < μ) :
    IsCantorSet (TeschlODE.Shared.tentRepellor μ) := by sorry

end TeschlODE.IntervalMaps

