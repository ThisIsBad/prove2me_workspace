import Mathlib
import Definitions.Def_PolicyGradTheory_ProjGA_MDP
import Definitions.Def_SuttonBartoRL_PolicyGradient_SoftmaxPolicy

namespace PolicyGradTheory.QNPG

open FoundationsML.ReinforcementLearning

/-- The log-linear policy class of §6.1.1 (p. 26). -/
noncomputable def logLinearPolicy {S A : Type} [Fintype A] {d : ℕ}
    (φ : S → A → EuclideanSpace ℝ (Fin d)) (θ : EuclideanSpace ℝ (Fin d))
    (s : S) (a : A) : ℝ :=
  SuttonBartoRL.PolicyGradient.softmaxPolicy
    (SuttonBartoRL.PolicyGradient.linearPref φ) θ s a

/-- The state-action PolicyGradTheory.ProjGA.visitation measure (19), pp. 27–28, starting from a
state-action pair sampled from `ν`. Its time-zero contribution is `ν (s,a)`;
the remaining terms take the specified first action, then follow `π`. -/
noncomputable def saVisitation {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (P : S → A → S → ℝ) (γ : ℝ)
    (ν : S × A → ℝ) (s : S) (a : A) : ℝ :=
  (1 - γ) * (ν (s, a) + ∑' t : ℕ, γ ^ (t + 1) *
    ∑ s₀ : S, ∑ a₀ : A, ν (s₀, a₀) *
      ∑ s₁ : S, P s₀ a₀ s₁ * OccupationDist π P s₁ t s * π s a)

/-- The on-policy state-action fitting distribution `d⁽ᵗ⁾` from (19)–(20),
packaged as a function on state-action pairs for use in `qLoss`. -/
noncomputable def onPolicyMeasure {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (P : S → A → S → ℝ) (γ : ℝ)
    (ν : S × A → ℝ) : S × A → ℝ :=
  fun p => saVisitation π P γ ν p.1 p.2

/-- The squared Q-prediction loss `L(w; θ, υ)` of §6.2, p. 27. -/
noncomputable def qLoss {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    {d : ℕ} (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ)
    (φ : S → A → EuclideanSpace ℝ (Fin d))
    (w θ : EuclideanSpace ℝ (Fin d)) (υ : S × A → ℝ) : ℝ :=
  ∑ s : S, ∑ a : A, υ (s, a) *
    (QFunction (logLinearPolicy φ θ) P r γ s a - inner ℝ w (φ s a)) ^ 2

/-- The comparator measure `d⋆ = d^{π⋆}_ρ × Unif_A` in Assumption 6.1, p. 28. -/
noncomputable def dstar {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (P : S → A → S → ℝ) (γ : ℝ) (ρ : S → ℝ) (πstar : S → A → ℝ)
    (p : S × A) : ℝ :=
  PolicyGradTheory.ProjGA.visitation πstar P γ ρ p.1 / (Fintype.card A : ℝ)

/-- The quadratic form `wᵀΣ_υw` in Assumption 6.2, p. 29. -/
noncomputable def quadForm {S A : Type} [Fintype S] [Fintype A] {d : ℕ}
    (φ : S → A → EuclideanSpace ℝ (Fin d)) (υ : S × A → ℝ)
    (w : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ s : S, ∑ a : A, υ (s, a) * (inner ℝ w (φ s a)) ^ 2

/-- The Q-NPG recurrence (20), p. 28, unfolded from `θ⁽⁰⁾ = 0`. -/
def qnpgParams {d : ℕ} {Ω : Type*} (η : ℝ)
    (w : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (t : ℕ) (ω : Ω) :
    EuclideanSpace ℝ (Fin d) :=
  η • ∑ i ∈ Finset.range t, w i ω

end PolicyGradTheory.QNPG
