import Mathlib
import Definitions.Def_Supermodularity_MDP_StochasticallyIncreasingOn

open MeasureTheory

namespace Supermodularity.MDP

/-- Lemma 3.9.4 (p. 161–162, PDF 174–175). A finite-horizon, nonstationary, discounted,
discrete-time Markov decision process with periods `i = 1, …, k`: state `t ∈ T i ⊆ Rᵐ`,
decision `x` restricted to the finite nonempty set `X i t ⊆ Rⁿ`, `S i = {(x,t) : t ∈ T i,
x ∈ X i t}`, return `r i x t`, discount `γ = 1/(1+β)`, next-state distribution `μ i x t`
on `Rᵐ`. Starting from `g k x t = r k x t`, `f` and `g` satisfy the backward recursion
`f i t = max {g i x t : x ∈ X i t}` (3.9.1) and, for `i < k`, `g i x t = r i x t +
γ ∫ f (i+1) w dμ (i x t) w` (3.9.2). If `X t' i ⊆ X t'' i` whenever `t' ≤ t''` in `T i`,
`r i x t` is increasing in `t` on the section of `S i` at `x` for all `x` and `i`, and
`F(x,t,i,·)` is stochastically increasing in `t` on the section of `S i` at `x` for all
`x` and `i`, then `f i t` is increasing in `t` on `T i` for each `i`. -/
theorem value_increasing_of_stochastically_increasing {n m : ℕ} (k : ℕ)
    (T : ℕ → Set (Fin m → ℝ)) (X : ℕ → (Fin m → ℝ) → Finset (Fin n → ℝ))
    (S : ℕ → Set ((Fin n → ℝ) × (Fin m → ℝ)))
    (hS : ∀ i, S i = {p : (Fin n → ℝ) × (Fin m → ℝ) | p.2 ∈ T i ∧ p.1 ∈ X i p.2})
    (r : ℕ → (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (μ : ℕ → (Fin n → ℝ) → (Fin m → ℝ) → Measure (Fin m → ℝ))
    (hμprob : ∀ i x t, IsProbabilityMeasure (μ i x t))
    (f : ℕ → (Fin m → ℝ) → ℝ) (g : ℕ → (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (hgk : ∀ x t, g k x t = r k x t)
    (hg : ∀ i, 1 ≤ i → i < k → ∀ x t, (x, t) ∈ S i →
      g i x t = r i x t + (1 / (1 + β)) * ∫ w, f (i + 1) w ∂ (μ i x t))
    (hfint : ∀ i, 1 ≤ i → i < k → ∀ x t, (x, t) ∈ S i → Integrable (f (i + 1)) (μ i x t))
    (hf : ∀ i, 1 ≤ i → i ≤ k → ∀ t ∈ T i,
      IsGreatest ((fun x => g i x t) '' (X i t : Set (Fin n → ℝ))) (f i t))
    (hXne : ∀ i, 1 ≤ i → i ≤ k → ∀ t ∈ T i, (X i t).Nonempty)
    (hXsub : ∀ i, 1 ≤ i → i ≤ k → ∀ ⦃t' t'' : Fin m → ℝ⦄, t' ∈ T i → t'' ∈ T i → t' ≤ t'' →
      X i t' ⊆ X i t'')
    (hrmono : ∀ i, 1 ≤ i → i ≤ k → ∀ x, MonotoneOn (fun t => r i x t) {t | (x, t) ∈ S i})
    (hFmono : ∀ i, 1 ≤ i → i ≤ k → ∀ x,
      Supermodularity.MDP.StochasticallyIncreasingOn {t | (x, t) ∈ S i} (μ i x)) :
    ∀ i, 1 ≤ i → i ≤ k → MonotoneOn (f i) (T i) := by sorry

end Supermodularity.MDP
