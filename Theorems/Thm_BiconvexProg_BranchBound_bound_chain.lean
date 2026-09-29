import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_run

namespace BiconvexProg.BranchBound

/-- The bound chain (p. 279): along a run, the best lower bounds `v_bᵏ` are nondecreasing, the
best upper bounds `V_bᵏ` are nonincreasing, and `v_bᵏ ≤ v* ≤ V_bᵏ` for every stage, where
`v* = φ(z*)` is the optimal value of Problem 𝒫. -/
theorem bound_chain {n : ℕ} {S : Set ((Fin n → ℝ) × (Fin n → ℝ))} {f g : (Fin n → ℝ) → ℝ}
    {Ω : Box n} (hP : IsProblemP S f g Ω)
    {nodes : ℕ → Multiset (Box n)} {sel : ℕ → Box n} {idx : ℕ → Fin n}
    {pt : ℕ → (Fin n → ℝ) × (Fin n → ℝ)} (hrun : IsRun S f g Ω nodes sel idx pt)
    (zstar : (Fin n → ℝ) × (Fin n → ℝ)) (hzs : zstar ∈ S ∩ Ω.toSet)
    (hmin : IsMinOn (objective f g) (S ∩ Ω.toSet) zstar) :
    Monotone (bestLower f g sel pt) ∧ Antitone (bestUpper f g pt) ∧
      ∀ k, bestLower f g sel pt k ≤ objective f g zstar ∧
        objective f g zstar ≤ bestUpper f g pt k := by sorry

end BiconvexProg.BranchBound
