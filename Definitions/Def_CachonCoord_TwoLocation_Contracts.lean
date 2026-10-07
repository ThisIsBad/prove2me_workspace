import Mathlib
import Definitions.Def_CachonCoord_TwoLocation_Model

namespace CachonCoord.TwoLocation
namespace Model

variable (M : Model)

/-- The linear transfer of §6.8.4 (p. 82),
`t_I I_r(s_r, s_s) + t_B^r B_r(s_r, s_s) + t_B^s B_s(s_s)`, for constants `t_I`, `t_B^r`,
`t_B^s`. A positive value is a payment from the supplier to the retailer (p. 82). -/
noncomputable def transfer (tI tBr tBs sr ss : ℝ) : ℝ :=
  tI * M.IR2 sr ss + tBr * M.BR2 sr ss + tBs * M.BS ss

/-- The retailer's cost under the transfer: `π_r(s_r, s_s)` minus the payment received. -/
noncomputable def contractedPiR (tI tBr tBs sr ss : ℝ) : ℝ :=
  M.piR sr ss - M.transfer tI tBr tBs sr ss

/-- The supplier's cost under the transfer: `π_s(s_r, s_s)` plus the payment made. -/
noncomputable def contractedPiS (tI tBr tBs sr ss : ℝ) : ℝ :=
  M.piS sr ss + M.transfer tI tBr tBs sr ss

/-- `t_I = (1 − λ) h_r`, (39), p. 84. -/
def tI (lam : ℝ) : ℝ := (1 - lam) * M.hr

/-- `t_B^r = β_r − λβ`, (40), p. 84. -/
def tBr (lam : ℝ) : ℝ := M.br - lam * M.beta

/-- `t_B^s = λ h_s F_s(s_s°)/(1 − F_s(s_s°))`, (41), p. 84, where `ssOpt` is the supplier's
optimal base stock `s_s°`. (`F_s(s_s°) < 1` always holds in the model since `F_s` is strictly
increasing on `[0, ∞)`, so the denominator is positive.) -/
noncomputable def tBs (lam ssOpt : ℝ) : ℝ := lam * M.hs * (M.FS ssOpt / (1 - M.FS ssOpt))

/-- The retailer's cost under the contracts (39)–(41) with parameter `λ`. -/
noncomputable def czPiR (lam ssOpt sr ss : ℝ) : ℝ :=
  M.contractedPiR (M.tI lam) (M.tBr lam) (M.tBs lam ssOpt) sr ss

/-- The supplier's cost under the contracts (39)–(41) with parameter `λ`. -/
noncomputable def czPiS (lam ssOpt sr ss : ℝ) : ℝ :=
  M.contractedPiS (M.tI lam) (M.tBr lam) (M.tBs lam ssOpt) sr ss

end Model
end CachonCoord.TwoLocation
