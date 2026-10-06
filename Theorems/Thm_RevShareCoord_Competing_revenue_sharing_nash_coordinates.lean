import Mathlib
import Definitions.Def_RevShareCoord_Competing_Game
import Definitions.Def_RevShareCoord_Competing_Model

namespace RevShareCoord.Competing

open Finset

/-- **Sec. 3.2, revenue sharing with competing retailers (p. 14).** Index convention:
`M.dR i j q = R_j^i(q̄) = ∂R_j/∂q_i`. Let `q̄^I` have positive entries and solve the first-order
system (6) of the integrated channel. Let `φ ∈ [0, 1]`, and let the supplier offer retailer `i`
the revenue-sharing contract `(φ, wᵢ(φ))` with `wᵢ(φ) = φ w_i^I = φ (c − Σ_{j≠i} R_j^i(q̄^I))`.
Then
1. `q̄^I` is a Nash equilibrium of the retailers' quantity game;
2. each retailer earns `π_{rᵢ}(q̄^I, φ, φ w̄^I) = φ π_{rᵢ}(q̄^I, w̄^I)`;
3. the supplier earns `π_s(q̄^I, φ, φ w̄^I) = (1 − φ) Π(q̄^I) + φ π_s(q̄^I, w̄^I)`. -/
theorem revenue_sharing_nash_coordinates {n : ℕ} (M : Model n) (qI : Fin n → ℝ)
    (hpos : ∀ i, 0 < qI i) (hfoc : M.FOC qI) (φ : ℝ) (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1) :
    IsNashEquilibrium M.R φ (fun k => φ * M.wI qI k) qI ∧
      (∀ i, retailerProfit M.R φ (fun k => φ * M.wI qI k) qI i =
        φ * retailerProfit M.R 1 (M.wI qI) qI i) ∧
      supplierProfit M.R M.c φ (fun k => φ * M.wI qI k) qI =
        (1 - φ) * systemProfit M.R M.c qI + φ * supplierProfit M.R M.c 1 (M.wI qI) qI := by sorry

end RevShareCoord.Competing

