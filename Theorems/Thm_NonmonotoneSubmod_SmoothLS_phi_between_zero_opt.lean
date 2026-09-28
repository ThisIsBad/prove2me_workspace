import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_OPT
import Definitions.Def_NonmonotoneSubmod_SmoothLS_BiasedSample

namespace NonmonotoneSubmod.SmoothLS

/-- §3.2, proof of Theorem 3.6, p. 1143 (Feige–Mirrokni–Vondrák 2011): "the value of `Φ(A)` is
always between `0` and `OPT`". For a nonnegative set function `f`, every bias `δ ∈ [-1, 1]` and
every `A ⊆ X`, `0 ≤ E[f(R(A, δ))] ≤ max_{S ⊆ X} f(S)`. -/
theorem phi_between_zero_opt {X : Type} [Fintype X] [DecidableEq X]
    (f : Finset X → ℝ) (hf0 : ∀ S, 0 ≤ f S) (δ : ℝ) (hδ0 : -1 ≤ δ) (hδ1 : δ ≤ 1)
    (A : Finset X) :
    0 ≤ Phi f δ A ∧ Phi f δ A ≤ NonmonotoneSubmod.Shared.OPT f := by sorry

end NonmonotoneSubmod.SmoothLS
