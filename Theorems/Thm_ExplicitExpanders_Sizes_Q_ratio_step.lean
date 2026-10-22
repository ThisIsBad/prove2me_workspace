import Mathlib
import Definitions.Def_ExplicitExpanders_Sizes_Q

namespace ExplicitExpanders.Sizes

/-- Proof of Lemma 2.2 (arXiv:2003.11673v1, p. 7), last sentence, with the printed
`Q(q₁, q₂, s − k₁, t − k₂)` corrected to `Q(q₁, q₂, s − k₁, t + k₂)`: if
for distinct primes, `μ > 0`, `k₁ > 0`, and `1 ≤ q₁^{k₁} / q₂^{k₂} ≤ 1 + μ`, then for all
`s > k₁` and `t ≥ 1` the ratio between
`Q(q₁, q₂, s, t)` and `Q(q₁, q₂, s − k₁, t + k₂)` lies between `1` and `(1 + μ)³`. -/
theorem Q_ratio_step {q₁ q₂ : ℕ} (hq₁ : q₁.Prime) (hq₂ : q₂.Prime) (hne : q₁ ≠ q₂)
    {μ : ℝ} (hμ : 0 < μ) {k₁ k₂ : ℕ} (hk₁ : 0 < k₁)
    (hlow : 1 ≤ (q₁ : ℝ) ^ k₁ / (q₂ : ℝ) ^ k₂) (hupp : (q₁ : ℝ) ^ k₁ / (q₂ : ℝ) ^ k₂ ≤ 1 + μ)
    {s t : ℕ} (hs : k₁ < s) (ht : 1 ≤ t) :
    1 ≤ (Q q₁ q₂ s t : ℝ) / (Q q₁ q₂ (s - k₁) (t + k₂) : ℝ) ∧
      (Q q₁ q₂ s t : ℝ) / (Q q₁ q₂ (s - k₁) (t + k₂) : ℝ) ≤ (1 + μ) ^ 3 := by sorry

end ExplicitExpanders.Sizes

