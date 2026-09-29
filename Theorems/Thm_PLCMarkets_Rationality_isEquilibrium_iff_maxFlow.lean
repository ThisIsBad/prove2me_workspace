import Mathlib
import Definitions.Def_PLCMarkets_Rationality_EquilibriumNetwork

namespace PLCMarkets.Rationality

/-- **LEMMA 3.1** (Vazirani–Yannakakis 2011, §3.2, p. 10:8). Under the standing assumptions of
Section 3 — positive prices (§3.1, "Given nonzero prices"), `Σ_j p_j = Σ_i e(i)` (§3), and
`unspent(i) ≥ 0`, `unsold(j) ≥ 0` (§3.2, first sentence) — the prices `p` are equilibrium prices
iff the max-flow value of the network `N(p)` equals `Σ_i unspent(i)`. (With positive prices, `k_i`
exists for every buyer, since the unbounded last segment of every `f^i_j` has infinite value.) -/
theorem isEquilibrium_iff_maxFlow {n g : ℕ} (M : FisherMarket n g) (p : Fin g → ℝ)
    (hp : ∀ j, 0 < p j)
    (hsum : ∑ j, p j = ∑ i, (M.budget i : ℝ))
    (hunspent : ∀ i, 0 ≤ M.unspent p i)
    (hunsold : ∀ j, 0 ≤ M.unsold p j) :
    M.IsEquilibrium p ↔ M.maxFlow p = ∑ i, M.unspent p i := by sorry

end PLCMarkets.Rationality
