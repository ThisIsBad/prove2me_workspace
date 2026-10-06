import Mathlib

namespace RevShareCoord.Single

/-- Integrated channel profit when both the quantity `q` and the retail price `p` are decision
variables (Sec. 3.1 and footnote 3, p. 11): revenue `Rev(q, p)` minus the linear cost `cq`. -/
def pqChainProfit (Rev : ℝ → ℝ → ℝ) (c q p : ℝ) : ℝ := Rev q p - c * q

/-- Retailer's profit under the revenue-sharing contract `{φ, w}` when he chooses both `q` and
`p`: `π_r(q, p, w, φ) = φ Rev(q, p) − wq` (Sec. 3.1, p. 11). -/
def pqRetailerProfit (Rev : ℝ → ℝ → ℝ) (φ w q p : ℝ) : ℝ := φ * Rev q p - w * q

end RevShareCoord.Single
