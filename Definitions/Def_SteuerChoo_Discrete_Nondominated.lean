import Mathlib

/-!
# Steuer–Choo (1983), §1: dominance, the nondominated set, maximizers of an objective

R. E. Steuer and E.-U. Choo, *An Interactive Weighted Tchebycheff Procedure for Multiple Objective
Programming*, Math. Programming 26 (1983), §1, p. 326.

The multiple objective program is `max {f₁(x) = z₁}, …, max {f_k(x) = z_k}, s.t. x ∈ S`, and `Z` is
the set of feasible criterion vectors (the image of `S` under the `fᵢ`). Here `Z` is given directly
as a finite set of vectors `Fin k → ℝ` (the paper's objective index `i = 1, …, k` is `i : Fin k`).
-/

namespace SteuerChoo.Discrete

/-- `Dominates z zbar`: `zᵢ ≥ z̄ᵢ` for all `i` and `zᵢ > z̄ᵢ` for at least one `i`
(Steuer–Choo 1983, §1, p. 326). -/
def Dominates {k : ℕ} (z zbar : Fin k → ℝ) : Prop :=
  (∀ i, zbar i ≤ z i) ∧ ∃ i, zbar i < z i

/-- The set `N ⊆ Z` of nondominated criterion vectors: `z̄ ∈ Z` such that no `z ∈ Z` dominates `z̄`
(Steuer–Choo 1983, §1, p. 326). -/
noncomputable def nondominated {k : ℕ} (Z : Finset (Fin k → ℝ)) : Finset (Fin k → ℝ) := by
  classical
  exact Z.filter (fun zbar => ¬ ∃ z ∈ Z, Dominates z zbar)

/-- `MaximizesObj Z i z`: the criterion vector `z ∈ Z` maximizes the `i`-th objective over `Z`. -/
def MaximizesObj {k : ℕ} (Z : Finset (Fin k → ℝ)) (i : Fin k) (z : Fin k → ℝ) : Prop :=
  z ∈ Z ∧ ∀ w ∈ Z, w i ≤ z i

end SteuerChoo.Discrete
