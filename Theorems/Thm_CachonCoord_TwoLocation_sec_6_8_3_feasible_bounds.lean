import Mathlib
import Definitions.Def_CachonCoord_TwoLocation_Model

namespace CachonCoord.TwoLocation

/-- §6.8.3, pp. 79–80 (the paragraph bounding the feasible strategies of the decentralized
game). With `ŝ_r` the minimizer of the retailer's single-location cost `c_r(y)`, characterized by
`F_r(ŝ_r) = β_r/(h_r + β_r)` (the page prints `β/(h_r + β)`; corrected, see the
natural-language statement): `ŝ_r > 0`, every best response `s_r(s_s)` of the retailer satisfies
`s_r(s_s) > ŝ_r`, and every best response `s_s(s_r)` of the supplier satisfies `s_s(s_r) > 0`. -/
theorem sec_6_8_3_feasible_bounds (M : Model) (shat : ℝ)
    (hshat : M.FR shat = M.br / (M.hr + M.br)) :
    0 < shat ∧
    (∀ ss sr : ℝ, IsMinOn (fun x => M.piR x ss) Set.univ sr → shat < sr) ∧
    (∀ sr ss : ℝ, IsMinOn (fun y => M.piS sr y) Set.univ ss → 0 < ss) := by sorry

end CachonCoord.TwoLocation

