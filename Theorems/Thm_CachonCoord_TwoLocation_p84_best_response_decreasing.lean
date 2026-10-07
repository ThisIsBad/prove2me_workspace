import Mathlib
import Definitions.Def_CachonCoord_TwoLocation_Model
import Definitions.Def_CachonCoord_TwoLocation_Contracts

namespace CachonCoord.TwoLocation

/-- §6.8.4, p. 84 (after (43)). Under the contracts (39)–(41) with `λ ∈ (0, 1]`, the retailer's
best response `s_r(s_s)` is decreasing in `s_s`, and along it the supplier's marginal cost is
`∂π_s(s_r(s_s), s_s)/∂s_s = F_s(s_s)(h_s − (1 − λ) c'(s_r(s_s)) + t_B^s) − t_B^s`
(the partial derivative in the supplier's own base stock, at `s_r = s_r(s_s)`). -/
theorem p84_best_response_decreasing (M : Model) (lam ssOpt : ℝ) (hlam0 : 0 < lam)
    (hlam1 : lam ≤ 1) :
    (∀ b1 b2 a1 a2 : ℝ, b1 ≤ b2 →
      IsMinOn (fun x => M.czPiR lam ssOpt x b1) Set.univ a1 →
      IsMinOn (fun x => M.czPiR lam ssOpt x b2) Set.univ a2 → a2 ≤ a1) ∧
    (∀ a b : ℝ, IsMinOn (fun x => M.czPiR lam ssOpt x b) Set.univ a →
      HasDerivAt (fun y => M.czPiS lam ssOpt a y)
        (M.FS b * (M.hs - (1 - lam) * M.cDeriv a + M.tBs lam ssOpt) - M.tBs lam ssOpt) b) := by sorry

end CachonCoord.TwoLocation

