import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_run

namespace BiconvexProg.BranchBound

/-- Finite termination (p. 278, stated there for stage 2): if at some stage the best lower and
upper bounds coincide, `v_bᵏ = V_bᵏ`, then every earlier stage point `(xˡ, yˡ)`, `l ≤ k`, that
attains `V_bᵏ` is a global solution of Problem 𝒫. -/
theorem finite_termination {n : ℕ} {S : Set ((Fin n → ℝ) × (Fin n → ℝ))}
    {f g : (Fin n → ℝ) → ℝ} {Ω : Box n} (hP : IsProblemP S f g Ω)
    {nodes : ℕ → Multiset (Box n)} {sel : ℕ → Box n} {idx : ℕ → Fin n}
    {pt : ℕ → (Fin n → ℝ) × (Fin n → ℝ)} (hrun : IsRun S f g Ω nodes sel idx pt)
    (k l : ℕ) (hl : l ≤ k) (hVl : objective f g (pt l) = bestUpper f g pt k)
    (heq : bestLower f g sel pt k = bestUpper f g pt k) :
    pt l ∈ S ∩ Ω.toSet ∧ IsMinOn (objective f g) (S ∩ Ω.toSet) (pt l) := by sorry

end BiconvexProg.BranchBound
