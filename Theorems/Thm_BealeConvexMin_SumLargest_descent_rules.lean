import Mathlib
import Definitions.Def_BealeConvexMin_SumLargest_sumLargest
import Definitions.Def_BealeConvexMin_SumLargest_Forms

namespace BealeConvexMin.SumLargest

/-- Beale (1955), Theorem 1 (a), second half, p. 179: "If these conditions are not all satisfied,
`C` can be decreased as follows". Each rule moves one coordinate (or all `u_f` equally) away from
zero, every other variable staying at zero, and `C` then drops strictly below `C(0, 0)` for all
small enough moves. `F` is the set of `l` with `z_l` free. -/
theorem descent_rules {r s : ℕ} (P : Forms r s) (τ : ℕ) (hτ : τ ≤ s) (F : Finset (Fin r)) :
    -- If `A_l + τ c_0l < 0`, increase `z_l` from zero.
    (∀ l : Fin r, P.A l + (τ : ℝ) * P.c0 l < 0 →
      ∃ ε > 0, ∀ t : ℝ, 0 < t → t < ε →
        P.C τ (Pi.single l t) 0 < P.C τ 0 0) ∧
    -- If `A_l + τ c_0l > 0`, decrease `z_l` from zero if it is free.
    (∀ l ∈ F, 0 < P.A l + (τ : ℝ) * P.c0 l →
      ∃ ε > 0, ∀ t : ℝ, 0 < t → t < ε →
        P.C τ (Pi.single l (-t)) 0 < P.C τ 0 0) ∧
    -- If `φ_f + τ θ_f < 0`, increase `u_f` from zero.
    (∀ f : Fin s, P.φ f + (τ : ℝ) * P.θ f < 0 →
      ∃ ε > 0, ∀ t : ℝ, 0 < t → t < ε →
        P.C τ 0 (Pi.single f t) < P.C τ 0 0) ∧
    -- If `φ_f + τ θ_f > 1`, decrease `u_f` from zero.
    (∀ f : Fin s, 1 < P.φ f + (τ : ℝ) * P.θ f →
      ∃ ε > 0, ∀ t : ℝ, 0 < t → t < ε →
        P.C τ 0 (Pi.single f (-t)) < P.C τ 0 0) ∧
    -- If `Σ_f (φ_f + τ θ_f) < τ - 1`, increase `u_1, …, u_s` equally from zero.
    (∑ f, (P.φ f + (τ : ℝ) * P.θ f) < (τ : ℝ) - 1 →
      ∃ ε > 0, ∀ t : ℝ, 0 < t → t < ε →
        P.C τ 0 (fun _ => t) < P.C τ 0 0) ∧
    -- If `Σ_f (φ_f + τ θ_f) > τ`, decrease `u_1, …, u_s` equally from zero.
    ((τ : ℝ) < ∑ f, (P.φ f + (τ : ℝ) * P.θ f) →
      ∃ ε > 0, ∀ t : ℝ, 0 < t → t < ε →
        P.C τ 0 (fun _ => -t) < P.C τ 0 0) := by sorry

end BealeConvexMin.SumLargest

