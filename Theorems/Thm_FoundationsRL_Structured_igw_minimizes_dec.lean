import Mathlib
import Definitions.Def_FoundationsRL_Structured_DEC
import Definitions.Def_FoundationsRL_Contextual_IsIGW

namespace FoundationsRL.Structured

/-- Proposition 14 (IGW minimizes the DEC) (Foster & Rakhlin, *Foundations of Reinforcement
Learning and Interactive Decision Making*, arXiv:2312.16730v1, p. 67): for the Multi-Armed
Bandit setting, where `Π = Fin A` and `F = ℝ^A` (all of `Fin A → ℝ`), the Inverse Gap
Weighting distribution `p = IGW_{4γ}(f̂)` (`FoundationsRL.Contextual.IsIGW`, Definition 4/Eq.
(3.36)) attains game value `(A−1)/(4γ)` in the min-max game defining `decγ(F, f̂)` (third
conjunct), this value is therefore an upper bound on `decGf` itself (first conjunct: `decGf`
is an infimum over all `q ∈ Δ(Π)`, so it is `≤` the value at the specific `q = p`), and it is
also a lower bound on the game value of *every* full-support `q ∈ Δ(Π)` (second conjunct).
Together these certify that `p` is optimal among the distributions for which the inner
`sSup` over `F = Set.univ` is honestly finite.

**Formalization note.** The book's own displayed claim is the single equality
`decγ(F,f̂) = (A−1)/(4γ)`, taking the `min_p` over the *whole* simplex `Δ(Π)`. That reading is
not provable in Lean's total real-number semantics: for any `q` with `q(π₀) = 0` at some arm
`π₀`, the inner `sSup` over the *unbounded* class `F = Set.univ` is genuinely `+∞` (no term of
the payoff ever penalizes moving `f(π₀) → ∞`), and `Real.sSup` returns Lean's junk value `0`
on that non-`BddAbove` set — which is `< (A−1)/(4γ)` and would make the book's literal
equality false for every `A ≥ 2`. The mathematical content the book actually uses is that the
`min_p` correctly avoids such degenerate, infinite-value `q`, which is exactly what the second
conjunct states directly (restricted to full-support `q`, where the game value is honestly
finite and IGW's own value is a genuine lower bound), together with the first conjunct's
upper bound and the third conjunct's exact value at IGW's own `p`. -/
theorem igw_minimizes_dec {A : ℕ} (fhat : Fin A → ℝ) (γ : ℝ) (hγ : 0 < γ)
    (piStar : (Fin A → ℝ) → Fin A) (hpiStar : ∀ f : Fin A → ℝ, ∀ π : Fin A, f π ≤ f (piStar f))
    (bstar : Fin A) (p : Fin A → ℝ) (hIGW : Contextual.IsIGW A fhat (4 * γ) bstar p) :
    decGf (Set.univ : Set (Fin A → ℝ)) piStar γ fhat ≤ ((A : ℝ) - 1) / (4 * γ) ∧
    (∀ q : Fin A → ℝ, (∀ π, 0 < q π) → (∑ π, q π = 1) →
      ((A : ℝ) - 1) / (4 * γ) ≤ sSup ((fun f : Fin A → ℝ =>
          ∑ π, q π * (f (piStar f) - f π - γ * (f π - fhat π) ^ 2)) ''
        (Set.univ : Set (Fin A → ℝ)))) ∧
    sSup ((fun f : Fin A → ℝ =>
        ∑ π, p π * (f (piStar f) - f π - γ * (f π - fhat π) ^ 2)) ''
      (Set.univ : Set (Fin A → ℝ))) = ((A : ℝ) - 1) / (4 * γ) := by sorry

end FoundationsRL.Structured
