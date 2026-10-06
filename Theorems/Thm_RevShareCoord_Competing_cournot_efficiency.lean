import Mathlib
import Definitions.Def_RevShareCoord_Competing_Game
import Definitions.Def_RevShareCoord_Competing_Cournot

namespace RevShareCoord.Competing

/-- **Sec. 4.1.2, efficiency at the supplier's optimal price (p. 20).** Cournot revenues (7) with
`0 ≤ β < 1`, `n ≥ 1` symmetric retailers and unit cost `0 < c < 1`. Let `q̄^N` be any Nash
equilibrium of the retailers' game at the common wholesale price `w* = (1 + c)/2` (no revenue
sharing), and `q̄^I` any maximizer of the system profit `Π` over `q̄ ≥ 0`. Then the efficiency of
the channel is
`Π(q̄^N)/Π(q̄^I) = 1 − 1/(2 + β(n − 1))²`. -/
theorem cournot_efficiency {n : ℕ} (β c : ℝ) (hn : 1 ≤ n) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hc0 : 0 < c) (hc1 : c < 1) (qN qI : Fin n → ℝ)
    (hN : IsNashEquilibrium (cournotRevenue β) 1 (fun _ => (1 + c) / 2) qN)
    (hI0 : ∀ i, 0 ≤ qI i)
    (hI : IsMaxOn (systemProfit (cournotRevenue β) c) {q : Fin n → ℝ | ∀ i, 0 ≤ q i} qI) :
    systemProfit (cournotRevenue β) c qN / systemProfit (cournotRevenue β) c qI =
      1 - 1 / (2 + β * ((n : ℝ) - 1)) ^ 2 := by sorry

end RevShareCoord.Competing

