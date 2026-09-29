import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_OPT
import Definitions.Def_NonmonotoneSubmod_Shared_SymmetricSetFun
import Definitions.Def_NonmonotoneSubmod_LocalSearch_LSAlgorithm

namespace NonmonotoneSubmod.LocalSearch

/-- Theorem 3.4 (Feige–Mirrokni–Vondrák 2011, p. 1141), in the explicit form of its proof.
Let `f ≥ 0` be submodular on a nonempty finite ground set `X` with `n = |X|`, and `ε > 0`.
(a) every terminated run of Algorithm LS returns `max(f(S), f(X \ S)) ≥ (1/3 − ε/n) OPT`;
(b) if `f` is symmetric, every terminated run ends at `S` with `f(S) ≥ (1/2 − ε/n) OPT`;
(c) if `n ≥ 2`, every run of `k` LS steps has `(1 + ε/n²)^k ≤ n`. -/
theorem ls_approximation {X : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    (f : Finset X → ℝ) (hf0 : ∀ S : Finset X, 0 ≤ f S) (hf : NonmonotoneSubmod.Shared.Submodular f)
    (ε : ℝ) (hε : 0 < ε) :
    (∀ (S : ℕ → Finset X) (k : ℕ), IsLSRun ε f S k → IsLSTerminal ε f (S k) →
        (1 / 3 - ε / (Fintype.card X : ℝ)) * NonmonotoneSubmod.Shared.OPT f ≤ lsOutput f (S k)) ∧
    (NonmonotoneSubmod.Shared.SymmetricSetFun f → ∀ (S : ℕ → Finset X) (k : ℕ), IsLSRun ε f S k →
        IsLSTerminal ε f (S k) →
        (1 / 2 - ε / (Fintype.card X : ℝ)) * NonmonotoneSubmod.Shared.OPT f ≤ f (S k)) ∧
    (2 ≤ Fintype.card X → ∀ (S : ℕ → Finset X) (k : ℕ), IsLSRun ε f S k →
        (1 + ε / (Fintype.card X : ℝ) ^ 2) ^ k ≤ (Fintype.card X : ℝ)) := by sorry

end NonmonotoneSubmod.LocalSearch

