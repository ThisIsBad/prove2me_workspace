import Mathlib
import Definitions.Def_FoundationsRL_RLBasics_Core

namespace FoundationsRL.RLBasics

/-- **Proposition 25 (Bellman Optimality)** (Foster–Rakhlin, arXiv:2312.16730v1, p. 83,
Prop. 25, Eqs. (5.6)–(5.9)): there is a deterministic policy `πdet`, greedy at every layer
`h < H` w.r.t. `Qstar` (Eq. (5.9)), whose `Q`-values satisfy the Bellman optimality
recursion `Q^⋆_h(s,a) = [T^M_h Q^⋆_{h+1}](s,a)` (Eqs. (5.8), (5.10)) and whose value
function equals `Vstar` at every layer and state, i.e. `πdet` is simultaneously optimal
among all of `Π^{rns}` at every state (Eq. (5.5)). -/
theorem bellman_optimality {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S]
    [DecidableEq A] {H : ℕ} (M : EpisodicMDP S A H) :
    ∃ πdet : ℕ → S → A,
      (∀ h, h < H → ∀ s : S, IsArgmax (Qstar M h s) (πdet h s)) ∧
      (∀ h, h < H → ∀ s : S, ∀ a : A, Qstar M h s a = bellmanOp M h (Qstar M (h + 1)) s a) ∧
      (∀ h, h ≤ H → ∀ s : S, V M (detPolicy πdet) h s = Vstar M h s) := by sorry

end FoundationsRL.RLBasics


