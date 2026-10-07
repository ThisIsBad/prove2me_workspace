import Mathlib

namespace SuttonBartoRL.PolicyGradient

variable {S A : Type} [Fintype A] {d : ℕ}

/-- (13.2), p. 322: the **soft-max in action preferences**,
`π(a | s, θ) = e^{h(s, a, θ)} / Σ_b e^{h(s, b, θ)}`, for numerical preferences `h(s, a, θ) ∈ ℝ`,
written `h θ s a`. -/
noncomputable def softmaxPolicy (h : EuclideanSpace ℝ (Fin d) → S → A → ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (s : S) (a : A) : ℝ :=
  Real.exp (h θ s a) / ∑ b, Real.exp (h θ s b)

/-- (13.3), p. 322: action preferences linear in features, `h(s, a, θ) = θᵀ x(s, a)`, for feature
vectors `x(s, a) ∈ ℝ^{d'}`. -/
noncomputable def linearPref (x : S → A → EuclideanSpace ℝ (Fin d))
    (θ : EuclideanSpace ℝ (Fin d)) (s : S) (a : A) : ℝ :=
  inner ℝ θ (x s a)

end SuttonBartoRL.PolicyGradient
