import Mathlib
import Definitions.Def_SteinitzExchange_Duality_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Duality_Conjugate

namespace SteinitzExchange.Duality

/-- Murota 1996, p. 294, Lemma 6.1, for any `f : B → ℝ` on a nonempty finite `B ⊆ ℤ^V`:
(1) `(−f)°(p) = −f•(−p)` for every `p ∈ ℝ^V`;
(2) `(−f)^(b) = −f̌(b)` for every `b ∈ B̄` (the closures regarded as functions on `B̄`). -/
theorem neg_conjugate_closure {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : B.Nonempty) (f : (V → ℤ) → ℝ) :
    (∀ p : V → ℝ, concaveConj B (fun x => -f x) p = -convexConj B f (-p)) ∧
    (∀ b ∈ hull B, concaveClosure B (fun x => -f x) b = -convexClosure B f b) := by sorry

end SteinitzExchange.Duality
