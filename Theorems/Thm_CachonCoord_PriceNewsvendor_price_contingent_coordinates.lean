import Mathlib
import Definitions.Def_CachonCoord_PriceNewsvendor_Model

namespace CachonCoord.PriceNewsvendor

/-- The p. 36–37 price-contingent buyback is equivalent to coordinating
revenue sharing without goodwill penalties. Both firms attain their maximum
profit at every integrated optimum; an endpoint share may make one indifferent. -/
theorem price_contingent_coordinates (M : Model) (lam : ℝ) (opt : ℝ × ℝ)
    (hgr : M.gr = 0) (hgs : M.gs = 0)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hopt_feasible : opt ∈ M.feasible)
    (hopt : IsMaxOn (fun x : ℝ × ℝ => M.Pi x.1 x.2) M.feasible opt) :
    (∀ x : ℝ × ℝ, x ∈ M.feasible →
      M.buybackRetailer (M.contingentW lam x.2) (M.contingentB lam x.2) x.1 x.2 =
        lam * M.Pi x.1 x.2 ∧
      M.revenueRetailer (M.revenueW lam) lam x.1 x.2 =
        lam * M.Pi x.1 x.2 ∧
      M.buybackSupplier (M.contingentW lam x.2) (M.contingentB lam x.2) x.1 x.2 =
        (1 - lam) * M.Pi x.1 x.2) ∧
    IsMaxOn (fun x : ℝ × ℝ =>
      M.buybackRetailer (M.contingentW lam x.2) (M.contingentB lam x.2) x.1 x.2)
      M.feasible opt ∧
    IsMaxOn (fun x : ℝ × ℝ =>
      M.buybackSupplier (M.contingentW lam x.2) (M.contingentB lam x.2) x.1 x.2)
      M.feasible opt := by sorry

end CachonCoord.PriceNewsvendor

