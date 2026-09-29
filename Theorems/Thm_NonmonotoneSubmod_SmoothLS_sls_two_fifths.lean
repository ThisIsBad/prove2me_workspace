import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_OPT
import Definitions.Def_NonmonotoneSubmod_SmoothLS_BiasedSample
import Definitions.Def_NonmonotoneSubmod_SmoothLS_SLSAlgorithm

namespace NonmonotoneSubmod.SmoothLS

/-- Theorem 3.6 (Feige–Mirrokni–Vondrák 2011, p. 1142; proof pp. 1142–1144), in the explicit form
of its proof. Let `f ≥ 0` be submodular on a ground set of `n = |X| ≥ 1` elements. A run of
Algorithm SLS is a sequence of sets `A 0 = ∅, A 1, …` where each `A (t+1)` arises from `A t` by
step 3 or step 4 applied to estimates `est t` of `ω_{A t, δ}` accurate within `± OPT/n²`.
1. (Running time.) For every bias `δ ∈ (0, 1]`, every run of `k` steps has `k < n²/δ`
   (for `δ = 1/3`: fewer than `3n²` iterations).
2. (Approximation.) For `δ = 1/3`, if the run has terminated at step `k`, the output
   `R(A k, δ′)` with `δ′ = 1/3` with probability `0.9` and `δ′ = -1` with probability `0.1` has
   expected value
   `0.9 E[f(R(A k, 1/3))] + 0.1 E[f(R(A k, -1))] ≥ (2/5 - 9/(5n)) OPT`. -/
theorem sls_two_fifths {X : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    (f : Finset X → ℝ) (hf0 : ∀ S, 0 ≤ f S) (hf : NonmonotoneSubmod.Shared.Submodular f) :
    (∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ (A : ℕ → Finset X) (est : ℕ → X → ℝ) (k : ℕ),
        A 0 = ∅ →
        (∀ t, t < k → Accurate f δ (A t) (est t)) →
        (∀ t, t < k → SLSStep f (est t) (A t) (A (t + 1))) →
        (k : ℝ) < (Fintype.card X : ℝ) ^ 2 / δ) ∧
    (∀ (A : ℕ → Finset X) (est : ℕ → X → ℝ) (k : ℕ),
        A 0 = ∅ →
        (∀ t, t ≤ k → Accurate f (1 / 3) (A t) (est t)) →
        (∀ t, t < k → SLSStep f (est t) (A t) (A (t + 1))) →
        SLSTerminated f (est k) (A k) →
        (2 / 5 - 9 / (5 * (Fintype.card X : ℝ))) * NonmonotoneSubmod.Shared.OPT f ≤
          9 / 10 * Phi f (1 / 3) (A k) + 1 / 10 * Phi f (-1) (A k)) := by sorry

end NonmonotoneSubmod.SmoothLS
