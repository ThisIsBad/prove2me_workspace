import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_DGPNash_WellSupported_Equilibria

namespace DGPNash.WellSupported

open Finset

/-- **Lemma 4.28** (= Lemma 2.1) (Daskalakis–Goldberg–Papadimitriou 2009, p. 243 and p. 199): let
`x` be an `ε`-approximate Nash equilibrium, `ε > 0`, of a game with `r ≥ 2` players and
nonnegative payoffs, and let `max{u}` be the largest payoff entry. Then the trimmed profile
`x̂ = trim u x ε k` with `k = 1 + 1/√ε` is a
`√ε · (√ε + 1 + 4(r − 1) max{u})`-approximately well-supported Nash equilibrium (in particular
a mixed profile). -/
theorem trim_is_well_supported {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (u : ι → (∀ i, S i) → ℝ) (hu : ∀ p s, 0 ≤ u p s) (hr : 2 ≤ Fintype.card ι)
    (x : ∀ i, S i → ℝ) (ε : ℝ) (hε : 0 < ε) (hx : IsEpsApproxNash u x ε) :
    IsEpsWellSupportedNash u (trim u x ε (1 + 1 / Real.sqrt ε))
      (Real.sqrt ε * (Real.sqrt ε + 1 + 4 * ((Fintype.card ι : ℝ) - 1) * maxPayoff u)) := by sorry

end DGPNash.WellSupported

