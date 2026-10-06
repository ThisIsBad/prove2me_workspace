import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_DGPNash_WellSupported_Equilibria

namespace DGPNash.WellSupported

open Finset

/-- **Claim 5** (Daskalakis–Goldberg–Papadimitriou 2009, pp. 243–244): if `x` is an
`ε`-approximate Nash equilibrium of a game with nonnegative payoffs and at least two players, then
for every `k > 0` and every player `p`, the mass
`z^p = Σ_j x^p_j · 𝒳_{\{𝒰^p_j < 𝒰^p_max − εk\}}` satisfies `z^p ≤ 1/k`. -/
theorem claim5_trimMass_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (u : ι → (∀ i, S i) → ℝ) (hu : ∀ p s, 0 ≤ u p s) (hr : 2 ≤ Fintype.card ι)
    (x : ∀ i, S i → ℝ) (ε : ℝ) (hx : IsEpsApproxNash u x ε) (k : ℝ) (hk : 0 < k) (p : ι) :
    trimMass u x ε k p ≤ 1 / k := by sorry

end DGPNash.WellSupported

