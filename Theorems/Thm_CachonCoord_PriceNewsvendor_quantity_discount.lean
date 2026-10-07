import Mathlib
import Definitions.Def_CachonCoord_PriceNewsvendor_Model

namespace CachonCoord.PriceNewsvendor

/-- The quantity discount of pp. 37–38, designed at the price component `p°` of an integrated
optimum `(q°, p°)`. (1) The retailer's profit identity of p. 38. (2) At `p = p°` the retailer
earns `λ(Π(q, p°) + gμ(p°)) - g_r μ(p°)` (the page's display omits the factor `λ`).
(3) If `g_s = 0`, for every `q` the retailer's optimal prices are exactly the chain's.
(4) Given `p°`, `q°` is optimal for the retailer and for the supplier. Joint optimality of
`(q°, p°)` for the retailer is not claimed (the page does not claim it). -/
theorem quantity_discount (M : Model) (lam : ℝ) (opt : ℝ × ℝ)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hopt_feasible : opt ∈ M.feasible)
    (hopt : IsMaxOn (fun x : ℝ × ℝ => M.Pi x.1 x.2) M.feasible opt) :
    (∀ q : ℝ, 0 ≤ q → ∀ p ∈ M.demand.prices,
      M.qdRetailer lam opt.2 q p =
        (p - M.v + M.gr) * M.S q p - lam * (M.c - M.v) * q - M.gr * M.mu p -
          ((1 - lam) * (opt.2 - M.v + M.g) - M.gs) * M.S q opt.2) ∧
    (∀ q : ℝ, 0 ≤ q →
      M.qdRetailer lam opt.2 q opt.2 =
        lam * (M.Pi q opt.2 + M.g * M.mu opt.2) - M.gr * M.mu opt.2) ∧
    (M.gs = 0 → ∀ q : ℝ, 0 ≤ q → ∀ p ∈ M.demand.prices,
      (IsMaxOn (fun t => M.qdRetailer lam opt.2 q t) M.demand.prices p ↔
        IsMaxOn (fun t => M.Pi q t) M.demand.prices p)) ∧
    IsMaxOn (fun q => M.qdRetailer lam opt.2 q opt.2) (Set.Ici 0) opt.1 ∧
    IsMaxOn (fun q => M.qdSupplier lam opt.2 q opt.2) (Set.Ici 0) opt.1 := by sorry

end CachonCoord.PriceNewsvendor

