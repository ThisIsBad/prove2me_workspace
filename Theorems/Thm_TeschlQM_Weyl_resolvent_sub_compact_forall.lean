import Mathlib
import Definitions.Def_TeschlQM_Shared_resolventSet

namespace TeschlQM.Weyl

/-- Teschl, Lemma 6.21 (first part), p. 147. Suppose `R_A(z) - R_B(z) ∈ ℭ(ℌ)` (6.35) for one
`z ∈ ρ(A) ∩ ρ(B)`. Then this holds for all `z ∈ ρ(A) ∩ ρ(B)`. The second part of the lemma,
`f(A) - f(B) ∈ ℭ(ℌ)` for `f ∈ C_∞(ℝ)`, needs the functional calculus and is not stated here. -/
theorem resolvent_sub_compact_forall {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A B : H →ₗ.[ℂ] H)
    (h : ∃ (z : ℂ) (RA RB : H →L[ℂ] H), TeschlQM.Shared.IsResolventAt A z RA ∧ TeschlQM.Shared.IsResolventAt B z RB ∧
      IsCompactOperator (RA - RB)) :
    ∀ (z : ℂ) (RA RB : H →L[ℂ] H), TeschlQM.Shared.IsResolventAt A z RA → TeschlQM.Shared.IsResolventAt B z RB →
      IsCompactOperator (RA - RB) := by sorry

end TeschlQM.Weyl
