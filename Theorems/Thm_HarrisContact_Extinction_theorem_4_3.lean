import Mathlib
import Definitions.Def_HarrisContact_Extinction_Model

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HarrisContact.Extinction

/-- Theorem 4.3 (p. 975): started from a finite set, the contact process makes finitely many jumps
on every [0, t] almost surely; in the chain model, the minimal transition function is honest. -/
theorem theorem_4_3 {d : ℕ} (hd : 1 ≤ d) (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 ≤ μ) (h0 : lam 0 = 0)
    (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k) :
    ∀ t : ℝ, 0 ≤ t → ∀ ξ : Config d, ∑' η : Config d, trans μ lam t ξ η = 1 := by sorry

end HarrisContact.Extinction

