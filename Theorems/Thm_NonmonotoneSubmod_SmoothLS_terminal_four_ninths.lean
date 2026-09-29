import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_OPT
import Definitions.Def_NonmonotoneSubmod_SmoothLS_BiasedSample

namespace NonmonotoneSubmod.SmoothLS

/-- §3.2, proof of Theorem 3.6, p. 1144, final chain (Feige–Mirrokni–Vondrák 2011). Let `f ≥ 0`
be submodular on a ground set of `n = |X| ≥ 1` elements, and let `A ⊆ X`, `B = X \ A`, satisfy
the terminal conditions `ω_{A,1/3}(x) ≥ -(3/n²) OPT` for all `x ∈ A` and
`ω_{A,1/3}(x) ≤ (3/n²) OPT` for all `x ∈ B`. Then, with `R = R(A, 1/3)`,
`E[f(R)] + (1/9) f(B) + (2/n) OPT ≥ (4/9) OPT`. -/
theorem terminal_four_ninths {X : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    (f : Finset X → ℝ) (hf0 : ∀ S, 0 ≤ f S) (hf : NonmonotoneSubmod.Shared.Submodular f) (A : Finset X)
    (hA : ∀ x, x ∈ A → -(3 / (Fintype.card X : ℝ) ^ 2 * NonmonotoneSubmod.Shared.OPT f) ≤ omegaB f A (1 / 3) x)
    (hB : ∀ x, x ∉ A → omegaB f A (1 / 3) x ≤ 3 / (Fintype.card X : ℝ) ^ 2 * NonmonotoneSubmod.Shared.OPT f) :
    4 / 9 * NonmonotoneSubmod.Shared.OPT f ≤ Phi f (1 / 3) A + 1 / 9 * f Aᶜ + 2 / (Fintype.card X : ℝ) * NonmonotoneSubmod.Shared.OPT f := by sorry

end NonmonotoneSubmod.SmoothLS
