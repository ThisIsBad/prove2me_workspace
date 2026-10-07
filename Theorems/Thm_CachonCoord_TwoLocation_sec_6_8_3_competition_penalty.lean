import Mathlib
import Definitions.Def_CachonCoord_TwoLocation_Model
import Definitions.Def_CachonCoord_TwoLocation_Game

namespace CachonCoord.TwoLocation

/-- §6.8.3, pp. 80–81 ("there always exists a positive competition penalty"). Without
contracts: (1) for every `s_s`, the retailer's optimal base stock (a minimizer of `c_r(·, s_s)`)
is strictly lower than the supply chain's (a minimizer of `c(·, s_s)`); (2) for an optimal pair
`{s_r°, s_s°}`, `s_r(s_s°) < s_r°`; (3) at every Nash equilibrium `{s_r*, s_s*}` of the
decentralized game the competition penalty `(Π(s*) − Π(s°))/Π(s°)` is positive. -/
theorem sec_6_8_3_competition_penalty (M : Model) :
    (∀ ss a b : ℝ, IsMinOn (fun x => M.cR2 x ss) Set.univ a →
      IsMinOn (fun x => M.c2 x ss) Set.univ b → a < b) ∧
    (∀ srOpt ssOpt : ℝ, IsMinOn (fun p : ℝ × ℝ => M.Pi p.1 p.2) Set.univ (srOpt, ssOpt) →
      ∀ a : ℝ, IsMinOn (fun x => M.piR x ssOpt) Set.univ a → a < srOpt) ∧
    (∀ srOpt ssOpt : ℝ, IsMinOn (fun p : ℝ × ℝ => M.Pi p.1 p.2) Set.univ (srOpt, ssOpt) →
      ∀ srN ssN : ℝ, IsNashMin M.piR M.piS srN ssN →
        0 < (M.Pi srN ssN - M.Pi srOpt ssOpt) / M.Pi srOpt ssOpt) := by sorry

end CachonCoord.TwoLocation

