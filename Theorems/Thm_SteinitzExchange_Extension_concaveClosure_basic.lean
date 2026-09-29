import Mathlib
import Definitions.Def_SteinitzExchange_Extension_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Extension_Exchange
import Definitions.Def_SteinitzExchange_Extension_ConcaveClosure

namespace SteinitzExchange.Extension

/-- Murota 1996, p. 285, Lemma 4.1, for any `g : B → ℝ` on a nonempty finite `B ⊆ ℤ^V`:
(1) `ĝ(x) ≥ g(x)` for `x ∈ B`;
(2) `max{ĝ(b) | b ∈ B̄} = max{g(x) | x ∈ B}` (the left maximum is attained);
(3) `argmax(ĝ) = conv(argmax(g))`, the argmax of `ĝ` taken over `B̄`. -/
theorem concaveClosure_basic {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : B.Nonempty) (g : (V → ℤ) → ℝ) :
    (∀ x ∈ B, g x ≤ concaveClosure B g (toReal x)) ∧
    ((∃ b ∈ hull B, concaveClosure B g b = B.sup' hB g) ∧
      ∀ b ∈ hull B, concaveClosure B g b ≤ B.sup' hB g) ∧
    argmaxOn (hull B) (concaveClosure B g) = hull (argmaxB B g) := by sorry

end SteinitzExchange.Extension
