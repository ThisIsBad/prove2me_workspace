import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_ThreeOpSplitting_Convergence_WeakConvergence

open InnerProductSpace ThreeOpSplitting.Convergence

namespace DouglasRachfordPPA.GenDR

/-- Theorem 3 (generalized proximal point algorithm), with the printed slips corrected:
`z (k+1) = (1 - ρ k) z k + ρ k w k` and `‖w k - J_{c_k T}(z k)‖ ≤ ε k`. The resolvent
`J_{c_k T}` is the map `J k` with `IsResolvent (c k) T (J k)`. -/
theorem generalized_proximal_point
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H → Set H) (hT : IsMaximalMonotone T)
    (c ρ ε : ℕ → ℝ) (J : ℕ → H → H) (hJ : ∀ k, IsResolvent (c k) T (J k))
    (z w : ℕ → H)
    (hz : ∀ k, z (k + 1) = (1 - ρ k) • z k + ρ k • w k)
    (hw : ∀ k, ‖w k - J k (z k)‖ ≤ ε k)
    (hε_nonneg : ∀ k, 0 ≤ ε k) (hε_sum : Summable ε)
    (hρ : ∃ ρ₁ ρ₂ : ℝ, 0 < ρ₁ ∧ ρ₂ < 2 ∧ ∀ k, ρ₁ ≤ ρ k ∧ ρ k ≤ ρ₂)
    (hc : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ k, c₀ ≤ c k) :
    ((zer T).Nonempty → ∃ zs ∈ zer T, WeakTendsto z zs) ∧
    (zer T = ∅ → ¬ Bornology.IsBounded (Set.range z)) := by sorry

end DouglasRachfordPPA.GenDR

