import Mathlib
import Definitions.Def_FoundationsRL_RLBasics_Core

namespace FoundationsRL.RLBasics

/-- **Lemma 15 (Error decomposition for optimistic policies)** (Foster–Rakhlin,
arXiv:2312.16730v1, p. 88, Lemma 15, Eq. (5.23)): given optimistic `Q`-value estimates
`Qhat` (`Qstar ≤ Qhat` pointwise at every layer `< H`, Eq. (5.22), with the terminal
convention `Qhat H ≡ 0`) and the deterministic policy `πdet` greedy w.r.t. `Qhat`, the
sub-optimality of `πdet` at any `s` is controlled by the `πdet`-roll-in expectation of
`Qhat`'s Bellman residuals. -/
theorem error_decomposition_optimistic {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
    [DecidableEq S] [DecidableEq A] {H : ℕ} (M : EpisodicMDP S A H) (Qhat : ℕ → S → A → ℝ)
    (hterm : ∀ s a, Qhat H s a = 0) (hopt : ∀ h, h < H → ∀ s a, Qstar M h s a ≤ Qhat h s a)
    (πdet : ℕ → S → A) (hgreedy : ∀ h, h < H → ∀ s : S, IsArgmax (Qhat h s) (πdet h s))
    (s : S) :
    Vstar M 0 s - V M (detPolicy πdet) 0 s ≤
      ∑ h ∈ Finset.range H,
        stateExp M (detPolicy πdet) s h (fun sh =>
          Qhat h sh (πdet h sh) - bellmanOp M h (Qhat (h + 1)) sh (πdet h sh)) := by sorry

end FoundationsRL.RLBasics


