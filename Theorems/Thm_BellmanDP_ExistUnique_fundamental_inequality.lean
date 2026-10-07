import Mathlib

open MeasureTheory

namespace BellmanDP.ExistUnique

/-- Bellman, *Dynamic Programming*, Ch. IV, § 2, Lemma 1, p. 118 (fundamental inequality).
Fix a state `p` and nonnegative measures `dG(p, q, ·)` on `ℝ^N` (`q ∈ S`). Let
`S₁(f₁, p, q) = g(p, q) + ∫_{r ∈ D} f₁(r) dG(p, q, r)` and
`S₂(F₁, p, q) = h(p, q) + ∫_{r ∈ D} F₁(r) dG(p, q, r)`, and let `f₂(p) = Sup_q S₁`,
`F₂(p) = Sup_q S₂` (genuine suprema). Then
`|f₂(p) − F₂(p)| ≤ Sup_q [|g(p, q) − h(p, q)| + ∫_{r ∈ D} |f₁(r) − F₁(r)| dG(p, q, r)]`,
stated as: every upper bound `M` of the bracket over `q` bounds `|f₂(p) − F₂(p)|`. -/
theorem fundamental_inequality {N : ℕ} {S : Type*}
    (D : Set (EuclideanSpace ℝ (Fin N))) (p : EuclideanSpace ℝ (Fin N))
    (G : EuclideanSpace ℝ (Fin N) → S → Measure (EuclideanSpace ℝ (Fin N)))
    (g h : EuclideanSpace ℝ (Fin N) → S → ℝ) (f₁ F₁ : EuclideanSpace ℝ (Fin N) → ℝ)
    (hf₁ : ∀ q : S, IntegrableOn f₁ D (G p q)) (hF₁ : ∀ q : S, IntegrableOn F₁ D (G p q))
    (f₂ F₂ : EuclideanSpace ℝ (Fin N) → ℝ)
    (hf₂ : IsLUB (Set.range fun q : S => g p q + ∫ r in D, f₁ r ∂(G p q)) (f₂ p))
    (hF₂ : IsLUB (Set.range fun q : S => h p q + ∫ r in D, F₁ r ∂(G p q)) (F₂ p))
    (M : ℝ) (hM : ∀ q : S, |g p q - h p q| + ∫ r in D, |f₁ r - F₁ r| ∂(G p q) ≤ M) :
    |f₂ p - F₂ p| ≤ M := by sorry

end BellmanDP.ExistUnique

