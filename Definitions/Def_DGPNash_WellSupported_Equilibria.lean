import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_DGPNash_NashMap_nashMap

/-!
# Daskalakis–Goldberg–Papadimitriou (2009), §2.1 and §4.7: approximate equilibria and the trim

C. Daskalakis, P. W. Goldberg, C. H. Papadimitriou, *The Complexity of Computing a Nash
Equilibrium*, SIAM J. Comput. 39(1):195–259 (2009), §2.1 (p. 199, Eq. (2)) and §4.7
(pp. 243–244, Eq. (27), Claim 5, the profile `x̂`).

A game in normal form is given by a finite type `ι` of players, a finite strategy type `S p` for
each player `p`, and payoffs `u : ι → (∀ i, S i) → ℝ` (`u p s` is the paper's `u^p_s`). Mixed
profiles, lotteries and expected payoffs are those of the published bundle `agt_games`.

**Formalization Note.** `purePayoff u x p j` is the paper's `𝒰^p_j = Σ_{s ∈ S_{-p}} u^p_{js} x_s`,
written as the expected payoff of `p` when `p` switches to the pure strategy `j`.
`maxPurePayoff u x p` is `𝒰^p_max = max_j 𝒰^p_j` (a supremum over the finite type `S p`; it is
the maximum when `S p` is nonempty, which every mixed profile forces). `maxPayoff u` is `max{u}`,
the largest entry of all payoff tables (a supremum over the finite types `ι` and `∀ i, S i`).
-/

namespace DGPNash.WellSupported

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

/-- The pure strategy `j` of player `p`, as a lottery on `S p`. -/
def pureStrategy {p : ι} (j : S p) : S p → ℝ := fun k => if k = j then 1 else 0

/-- `𝒰^p_max = max_j 𝒰^p_j` (p. 243). -/
noncomputable def maxPurePayoff (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) (p : ι) : ℝ :=
  ⨆ j : S p, DGPNash.NashMap.purePayoff u x p j

/-- `max{u}`: the maximum entry in the payoff tables of the game, over all players and all pure
strategy profiles (Lemma 4.28, p. 243). -/
noncomputable def maxPayoff (u : ι → (∀ i, S i) → ℝ) : ℝ :=
  ⨆ p : ι, ⨆ s : (∀ i, S i), u p s

/-- **ε-approximate Nash equilibrium** (p. 199; Eq. (27), p. 243): `x` is a mixed profile and, for
every player `p` and every mixed strategy `y` of `p`, the expected payoff of `p` under `x` is at
least the expected payoff of `p` when `p` alone switches to `y`, minus `ε`. -/
def IsEpsApproxNash (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) (ε : ℝ) : Prop :=
  AGT.IsMixedProfile x ∧
    ∀ (p : ι) (y : S p → ℝ), AGT.IsLottery y →
      AGT.expectedPayoff u (Function.update x p y) p - ε ≤ AGT.expectedPayoff u x p

/-- **ε-approximately well-supported Nash equilibrium** (Eq. (2), p. 199): `x` is a mixed profile
and, for every player `p` and strategies `j, j'` of `p`, if `𝒰^p_j > 𝒰^p_{j'} + ε` then
`x^p_{j'} = 0`. -/
def IsEpsWellSupportedNash (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) (ε : ℝ) : Prop :=
  AGT.IsMixedProfile x ∧
    ∀ (p : ι) (j j' : S p), DGPNash.NashMap.purePayoff u x p j > DGPNash.NashMap.purePayoff u x p j' + ε → x p j' = 0

/-- `z^p = Σ_{j ∈ S_p} x^p_j · 𝒳_{\{𝒰^p_j < 𝒰^p_max − εk\}}` (Claim 5, pp. 243–244): the mass `x`
puts on strategies of `p` whose payoff is more than `εk` below the best response. -/
noncomputable def trimMass (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) (ε k : ℝ) (p : ι) : ℝ :=
  ∑ j : S p, if DGPNash.NashMap.purePayoff u x p j < maxPurePayoff u x p - ε * k then x p j else 0

/-- The trimmed profile `x̂` (proof of Lemma 4.28, p. 244):
`x̂^p_j = x^p_j / (1 − z^p)` if `𝒰^p_j ≥ 𝒰^p_max − εk`, and `x̂^p_j = 0` otherwise. -/
noncomputable def trim (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) (ε k : ℝ) :
    ∀ i, S i → ℝ :=
  fun p j =>
    if DGPNash.NashMap.purePayoff u x p j ≥ maxPurePayoff u x p - ε * k then
      x p j / (1 - trimMass u x ε k p)
    else 0

end DGPNash.WellSupported
