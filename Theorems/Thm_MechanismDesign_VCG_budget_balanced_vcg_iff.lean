import Mathlib
import Definitions.Def_MechanismDesign_VCG_Model

namespace MechanismDesign.VCG

/-- Börgers, Proposition 7.10 (p.138), after Holmström (1977) via Milgrom (2004): with at least
two agents, let `q` be efficient. A budget-balanced VCG mechanism with decision rule `q` exists
if and only if there are functions `fᵢ : Θ₋ᵢ → ℝ` with `∑ᵢ uᵢ(q(θ), θᵢ) = ∑ᵢ fᵢ(θ₋ᵢ)` for all
`θ ∈ Θ`. -/
theorem budget_balanced_vcg_iff {ι A : Type*} {Θ : ι → Type*} [Fintype ι] [DecidableEq ι]
    (u : ∀ i, A → Θ i → ℝ) (hN : 2 ≤ Fintype.card ι) (q : (∀ i, Θ i) → A)
    (hq : IsEfficient u q) :
    (∃ t : ι → (∀ i, Θ i) → ℝ,
        IsVCG u (⟨q, t⟩ : DirectMechanism Θ A) ∧ BudgetBalanced (⟨q, t⟩ : DirectMechanism Θ A)) ↔
      ∃ f : ∀ i, Others Θ i → ℝ, ∀ θ : ∀ j, Θ j,
        ∑ i, u i (q θ) (θ i) = ∑ i, f i (restrict θ i) := by sorry

end MechanismDesign.VCG

