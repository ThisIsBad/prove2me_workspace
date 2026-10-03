import Mathlib
import Definitions.Def_TeschlODE_Shared_tentRepellor

namespace TeschlODE.Horseshoe

/-- Teschl, §13.1, p. 332, (13.8): the invariant set of the Smale horseshoe,
`Λ = Λ₋ ∩ Λ₊ = Λ(T_{1/λ}) × Λ(T_µ)`, where `Λ(T_µ)` is the set (11.18) of points whose orbit under
the tent map `T_µ` stays in `[0, 1]`. -/
def horseshoeSet (lam μ : ℝ) : Set (ℝ × ℝ) :=
  TeschlODE.Shared.tentRepellor (1 / lam) ×ˢ TeschlODE.Shared.tentRepellor μ

end TeschlODE.Horseshoe
