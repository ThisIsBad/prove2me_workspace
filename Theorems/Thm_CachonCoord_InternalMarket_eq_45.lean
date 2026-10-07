import Mathlib
import Definitions.Def_CachonCoord_InternalMarket_Revenue
import Definitions.Def_CachonCoord_InternalMarket_Model

namespace CachonCoord.InternalMarket

open MeasureTheory

/-- Eq. (45), §6.9.1, p. 93 (Cachon 2003, 3rd draft). Let
`K = E[(A₁^η + A₂^η)^{1/η} Y^{(η−1)/η}]` (assumed integrable). Then, on `e ≥ 0`:
1. total expected supply chain profit is `Π(e) = E[π(A, Ye)] − c(e) = K e^{(η−1)/η} − c(e)`;
2. `Π` is strictly concave on `[0, ∞)`;
3. for `e > 0`, `Π'(e) = ((η − 1)/η) e^{−1/η} K − c'(e)`;
4. an effort `e° > 0` maximizes `Π` over `[0, ∞)` if and only if
   `((η − 1)/η) (e°)^{−1/η} K − c'(e°) = 0`. -/
theorem eq_45 {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω)
    (hint : Integrable (fun ω => (M.A₁ ω ^ M.η + M.A₂ ω ^ M.η) ^ (1 / M.η) *
      M.Y ω ^ ((M.η - 1) / M.η)) M.P) :
    (∀ e : ℝ, 0 ≤ e → M.chainProfit e = M.K * e ^ ((M.η - 1) / M.η) - M.c e) ∧
    StrictConcaveOn ℝ (Set.Ici 0) M.chainProfit ∧
    (∀ e : ℝ, 0 < e →
      HasDerivAt M.chainProfit ((M.η - 1) / M.η * e ^ (-1 / M.η) * M.K - M.c' e) e) ∧
    ∀ eo : ℝ, 0 < eo →
      (IsMaxOn M.chainProfit (Set.Ici 0) eo ↔
        (M.η - 1) / M.η * eo ^ (-1 / M.η) * M.K - M.c' eo = 0) := by sorry

end CachonCoord.InternalMarket

