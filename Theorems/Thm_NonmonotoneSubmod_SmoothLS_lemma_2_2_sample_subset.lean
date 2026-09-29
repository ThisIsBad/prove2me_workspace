import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular

namespace NonmonotoneSubmod.SmoothLS

/-- Lemma 2.2 (Feige–Mirrokni–Vondrák 2011, p. 1137). Let `g : 2^X → ℝ` be submodular, `A ⊆ X`,
and let `A(p)` be the random subset of `A` containing each element of `A` independently with
probability `p ∈ [0,1]`. Then `E[g(A(p))] ≥ (1 - p) g(∅) + p g(A)`. The expectation is written as
the exact finite sum over `T ⊆ A` with weight `p^|T| (1-p)^|A \ T|`. -/
theorem lemma_2_2_sample_subset {X : Type} [Fintype X] [DecidableEq X]
    (g : Finset X → ℝ) (hg : NonmonotoneSubmod.Shared.Submodular g) (A : Finset X) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (1 - p) * g ∅ + p * g A ≤
      ∑ T ∈ A.powerset, p ^ T.card * (1 - p) ^ (A \ T).card * g T := by sorry

end NonmonotoneSubmod.SmoothLS
