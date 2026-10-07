import Mathlib
import Definitions.Def_CachonCoord_TwoLocation_Model
import Definitions.Def_CachonCoord_TwoLocation_Contracts

namespace CachonCoord.TwoLocation

/-- §6.8.4, p. 84, Eqs. (42)–(43). Under the contracts (39)–(41) with parameter `λ` (any
`λ` and any value `s_s°` used in (41)), for all base stocks `(s_r, s_s)` the retailer's cost is
`λ c(s_r, s_s) − t_B^s B_s(s_s)` (the page prints `λΠ(s_r, s_s)` in (42); corrected) and the
supplier's cost is `(h_s + t_B^s) I_s(s_s) + (1 − λ) c(s_r, s_s) + t_B^s (μ_s − s_s)`. -/
theorem eq_42_43 (M : Model) (lam ssOpt : ℝ) :
    ∀ sr ss : ℝ,
      M.czPiR lam ssOpt sr ss = lam * M.c2 sr ss - M.tBs lam ssOpt * M.BS ss ∧
      M.czPiS lam ssOpt sr ss = (M.hs + M.tBs lam ssOpt) * M.IS ss + (1 - lam) * M.c2 sr ss
        + M.tBs lam ssOpt * (M.muS - ss) := by sorry

end CachonCoord.TwoLocation

