import Mathlib
import Definitions.Def_YoungConventions_AdaptivePlay_WeaklyAcyclic
import Definitions.Def_YoungConventions_AdaptivePlay_LGamma
import Definitions.Def_YoungConventions_AdaptivePlay_IsBestReplyDistribution
import Definitions.Def_YoungConventions_AdaptivePlay_adaptivePlay
import Definitions.Def_YoungConventions_AdaptivePlay_IsConvention

open Filter Topology Classical

namespace YoungConventions.AdaptivePlay

/-- **Theorem 1** (Young 1993, *The Evolution of Conventions*, Econometrica 61:57–84, Theorem 1,
p. 64, PDF p. 9): "Let `Γ` be a weakly acyclic `n`-person game. If `k ≤ m/(L_Γ + 2)`, then adaptive
play converges almost surely to a convention."

Let `Γ` be a finite game (finite set of players, finite nonempty strategy sets, real payoffs) that
is weakly acyclic, let `L_Γ` be the maximum over strategy tuples of the length of a shortest
best-reply path to a strict Nash equilibrium, and let `1 ≤ k` and `k(L_Γ + 2) ≤ m`. For every
best-reply distribution `p` and every initial state `h`, the probability that adaptive play `P⁰`
started at `h` is in a convention at time `t` tends to `1` as `t → ∞`.

**Formalization Note.** (1) "Converges almost surely to a convention" is encoded through the
`t`-step transition probabilities: `∑_{h′ convention} (P⁰)ᵗ_{hh′} → 1`. Because conventions are
absorbing (`absorbing_iff_convention`), the event "in a convention at time `t`" increases in `t`,
and its probability tending to `1` is equivalent to almost-sure eventual absorption in a
convention, for every initial state. (2) `k ≤ m/(L_Γ + 2)` is written `k * (L_Γ + 2) ≤ m` in `ℕ`
(equivalent, no truncating division); together with `1 ≤ k` it gives the paper's `1 ≤ k ≤ m`.
(3) The theorem quantifies over every best-reply distribution: the sampling law is not fixed. -/
theorem theorem_1 {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)]
    (u : ι → (∀ i, S i) → ℝ) (hu : WeaklyAcyclic u)
    (k m : ℕ) [NeZero m] (hk : 1 ≤ k) (hkm : k * (LGamma u + 2) ≤ m)
    (p : ∀ i, History S m → S i → ℝ) (hp : IsBestReplyDistribution u k p)
    (h : History S m) :
    Tendsto (fun t : ℕ => ∑ h' ∈ Finset.univ.filter (fun h' : History S m => IsConvention u h'),
      (adaptivePlay p ^ t) h h') atTop (𝓝 1) := by sorry

end YoungConventions.AdaptivePlay

