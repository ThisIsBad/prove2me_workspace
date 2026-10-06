import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_DGPNash_WellSupported_Equilibria

namespace DGPNash.WellSupported

open Finset

/-- **Claim 6** (Daskalakis–Goldberg–Papadimitriou 2009, p. 244): if `x` is an
`ε`-approximate Nash equilibrium of a game with nonnegative payoffs and at least two players, and
`k > 1`, then for every player `p` the trimmed profile `x̂ = trim u x ε k` satisfies
`Σ_{j ∈ S_p} |x^p_j − x̂^p_j| ≤ 2/(k − 1)`. -/
theorem claim6_trim_l1_dist {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (u : ι → (∀ i, S i) → ℝ) (hu : ∀ p s, 0 ≤ u p s) (hr : 2 ≤ Fintype.card ι)
    (x : ∀ i, S i → ℝ) (ε : ℝ) (hx : IsEpsApproxNash u x ε) (k : ℝ) (hk : 1 < k) (p : ι) :
    ∑ j : S p, |x p j - trim u x ε k p j| ≤ 2 / (k - 1) := by sorry

end DGPNash.WellSupported

