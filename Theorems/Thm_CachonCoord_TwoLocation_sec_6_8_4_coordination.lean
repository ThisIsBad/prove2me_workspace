import Mathlib
import Definitions.Def_CachonCoord_TwoLocation_Model
import Definitions.Def_CachonCoord_TwoLocation_Contracts
import Definitions.Def_CachonCoord_TwoLocation_Game

namespace CachonCoord.TwoLocation

/-- §6.8.4, pp. 84–85, the coordination result for the Cachon–Zipkin linear transfers. Let
`{s_r°, s_s°}` minimize the supply chain's cost `Π` with `s_s° > 0`, and let `λ ∈ (0, 1]`. Under
the contracts (39) `t_I = (1 − λ)h_r`, (40) `t_B^r = β_r − λβ`,
(41) `t_B^s = λh_s F_s(s_s°)/(1 − F_s(s_s°))`:
1. (42)–(43): the retailer's cost is `λ c(s_r, s_s) − t_B^s B_s(s_s)` (printed `λΠ`; corrected) and
   the supplier's is `(h_s + t_B^s) I_s(s_s) + (1 − λ) c(s_r, s_s) + t_B^s (μ_s − s_s)`;
2. `{s_r°, s_s°}` is a Nash equilibrium of the contracted game;
3. it is the unique Nash equilibrium. -/
theorem sec_6_8_4_coordination (M : Model) (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1)
    (srOpt ssOpt : ℝ)
    (hopt : IsMinOn (fun p : ℝ × ℝ => M.Pi p.1 p.2) Set.univ (srOpt, ssOpt))
    (hss : 0 < ssOpt) :
    (∀ sr ss : ℝ,
      M.czPiR lam ssOpt sr ss = lam * M.c2 sr ss - M.tBs lam ssOpt * M.BS ss ∧
      M.czPiS lam ssOpt sr ss = (M.hs + M.tBs lam ssOpt) * M.IS ss + (1 - lam) * M.c2 sr ss
        + M.tBs lam ssOpt * (M.muS - ss)) ∧
    IsNashMin (M.czPiR lam ssOpt) (M.czPiS lam ssOpt) srOpt ssOpt ∧
    (∀ sr ss : ℝ, IsNashMin (M.czPiR lam ssOpt) (M.czPiS lam ssOpt) sr ss →
      sr = srOpt ∧ ss = ssOpt) := by sorry

end CachonCoord.TwoLocation

