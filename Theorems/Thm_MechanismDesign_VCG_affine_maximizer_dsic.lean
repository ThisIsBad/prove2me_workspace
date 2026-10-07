import Mathlib
import Definitions.Def_MechanismDesign_VCG_Model

namespace MechanismDesign.VCG

/-- Börgers, Proposition 7.8 (p.136): in the setting of Proposition 7.7 (`A` finite, every
agent's type set unrestricted), suppose `q` satisfies the characterization of Proposition 7.7:
there are `kᵢ > 0` and `F : A → ℝ` with
`∑ᵢ kᵢ uᵢ(q(θ), θᵢ) + F(q(θ)) ≥ ∑ᵢ kᵢ uᵢ(a, θᵢ) + F(a)` for all `θ ∈ Θ` and all `a ∈ A`.
Then there are transfer rules making `(q, t₁, …, t_N)` dominant strategy incentive-compatible. -/
theorem affine_maximizer_dsic {ι A : Type*} {Θ : ι → Type*} [Fintype ι] [DecidableEq ι]
    [Finite A] (u : ∀ i, A → Θ i → ℝ)
    (hrich : ∀ (i : ι) (ν : A → ℝ), ∃ x : Θ i, ∀ a, u i a x = ν a)
    (q : (∀ i, Θ i) → A) (k : ι → ℝ) (hk : ∀ i, 0 < k i) (F : A → ℝ)
    (hmax : ∀ (θ : ∀ j, Θ j) (a : A),
      ∑ i, k i * u i (q θ) (θ i) + F (q θ) ≥ ∑ i, k i * u i a (θ i) + F a) :
    ∃ t : ι → (∀ i, Θ i) → ℝ, DSIC u ⟨q, t⟩ := by sorry

end MechanismDesign.VCG

