import Mathlib

namespace FoundationsRL.Structured

/-- Lemma 9 (Decoupling), general form (Foster & Rakhlin, *Foundations of Reinforcement
Learning and Interactive Decision Making*, arXiv:2312.16730v1, p. 32, Eq. (2.24) — the
"more general result" the proof of Lemma 9 establishes and which Chapter 4 invokes for
arbitrary reference distributions, not just the posterior `µ_t` of the boxed statement (2.23)):
for a finite class of models `F` (indexed by `ι`, via `f : ι → (Fin A → ℝ)` with every `f i ∈
F`), any distribution `ν` over the models, and any `f̄ : Fin A → ℝ`, if `p` is the marginal
distribution over decisions induced by drawing a model `i ∼ ν` and playing its maximizer
`piStar (f i)`, then

`E_{i∼ν}[f_i(π_{f_i}) − f̄(π_{f_i})] ≤ √(A · E_{i∼ν} E_{π∼p}[(f_i(π) − f̄(π))²])`.

This is the decoupling step: on the left, the model `i` and the decision `π_{f_i}` are coupled;
on the right, `π` is drawn from the marginal `p`, independent of the specific draw of `i`. -/
theorem decoupling_lemma {A : ℕ} {ι : Type*} [Fintype ι] (F : Set (Fin A → ℝ))
    (f : ι → Fin A → ℝ) (hf : ∀ i, f i ∈ F)
    (piStar : (Fin A → ℝ) → Fin A) (hpiStar : ∀ i, ∀ π, f i π ≤ f i (piStar (f i)))
    (ν : ι → ℝ) (hν_nonneg : ∀ i, 0 ≤ ν i) (hν_sum : ∑ i, ν i = 1)
    (p : Fin A → ℝ) (hp : ∀ π, p π = ∑ i, ν i * (if piStar (f i) = π then 1 else 0))
    (fbar : Fin A → ℝ) :
    ∑ i, ν i * (f i (piStar (f i)) - fbar (piStar (f i))) ≤
      Real.sqrt ((A : ℝ) * ∑ i, ν i * ∑ π, p π * (f i π - fbar π) ^ 2) := by sorry

end FoundationsRL.Structured
