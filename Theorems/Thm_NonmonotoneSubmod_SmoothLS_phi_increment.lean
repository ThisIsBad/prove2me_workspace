import Mathlib
import Definitions.Def_NonmonotoneSubmod_SmoothLS_BiasedSample

namespace NonmonotoneSubmod.SmoothLS

/-- §3.2, proof of Theorem 3.6, p. 1143, first display (Feige–Mirrokni–Vondrák 2011). For every
real set function `f`, every bias `δ`, every `A ⊆ X` and every element `x`, with
`Φ_δ(A) = E[f(R(A, δ))]`:
* if `x ∉ A` (step 3 adds `x`), then `Φ_δ(A ∪ {x}) - Φ_δ(A) = δ ω_{A,δ}(x)`;
* if `x ∈ A` (step 4 removes `x`), then `Φ_δ(A \ {x}) - Φ_δ(A) = -δ ω_{A,δ}(x)`. -/
theorem phi_increment {X : Type} [Fintype X] [DecidableEq X]
    (f : Finset X → ℝ) (δ : ℝ) (A : Finset X) (x : X) :
    (x ∉ A → Phi f δ (insert x A) - Phi f δ A = δ * omegaB f A δ x) ∧
    (x ∈ A → Phi f δ (A.erase x) - Phi f δ A = -(δ * omegaB f A δ x)) := by sorry

end NonmonotoneSubmod.SmoothLS
