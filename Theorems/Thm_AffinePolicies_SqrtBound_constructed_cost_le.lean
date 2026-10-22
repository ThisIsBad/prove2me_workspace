import Mathlib
import Definitions.Def_AffinePolicies_SqrtBound_Setting

open Matrix

namespace AffinePolicies.SqrtBound

theorem constructed_cost_le {m n₁ n₂ : ℕ} (A : Matrix (Fin m) (Fin n₁) ℝ)
    (B : Matrix (Fin m) (Fin n₂) ℝ) (c : Fin n₁ → ℝ) (d : Fin n₂ → ℝ) (U : Set (Fin m → ℝ))
    (hd : 0 ≤ d) (hUnn : ∀ b ∈ U, 0 ≤ b)
    (μ : Fin m → ℝ) (hμ : ∀ j, IsGreatest ((fun b : Fin m → ℝ => b j) '' U) (μ j))
    (hμpos : ∀ j, 0 < μ j)
    (bstar : Fin m → Fin m → ℝ) (hbstar : ∀ j, bstar j ∈ U ∧ bstar j j = μ j)
    (K : ℕ) (u : ℕ → Fin m → ℝ) (hrun : IsRun U μ K u)
    (xs : Fin n₁ → ℝ) (ys : (Fin m → ℝ) → Fin n₂ → ℝ) (hfs : AffinePolicies.Simplex.Feasible A B U xs ys) :
    ∀ t : ℝ, AffinePolicies.Simplex.CostLE c d U xs ys t →
      AffinePolicies.Simplex.CostLE c d U ((3 * Real.sqrt m) • xs)
        (AffinePolicies.Simplex.affinePolicy (thmPolicyP ys bstar μ (J1 μ u K)) (thmPolicyq ys u K))
        (3 * Real.sqrt m * t) := by sorry

end AffinePolicies.SqrtBound

