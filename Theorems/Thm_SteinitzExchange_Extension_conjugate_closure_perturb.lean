import Mathlib
import Definitions.Def_SteinitzExchange_Extension_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Extension_Exchange
import Definitions.Def_SteinitzExchange_Extension_ConcaveClosure

namespace SteinitzExchange.Extension

/-- Murota 1996, p. 285, Lemma 4.2, for any `g : B → ℝ` on a nonempty finite `B ⊆ ℤ^V`:
(1) `(g[p₀])°(p) = g°(p − p₀)`;
(2) `(g[p₀])^(b) = ĝ[p₀](b) = ĝ(b) + ⟨p₀, b⟩` for `b ∈ B̄`. -/
theorem conjugate_closure_perturb {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : B.Nonempty) (g : (V → ℤ) → ℝ) (p₀ : V → ℝ) :
    (∀ p : V → ℝ, concaveConj B (perturb g p₀) p = concaveConj B g (p - p₀)) ∧
    (∀ b ∈ hull B, concaveClosure B (perturb g p₀) b = concaveClosure B g b + pairing p₀ b) := by sorry

end SteinitzExchange.Extension
