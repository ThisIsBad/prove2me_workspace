import Mathlib
import Definitions.Def_Disjunctive_Polymatroids_Basic

namespace Disjunctive.Polymatroids

/-- Proposition 13.23 (Balas §13.8, p. 231-232): if `π` is an extreme point of `Π`, then `π_j =
Σ_{A∋j} u_A` for `j∈N`, with `u` extreme in `U`. -/
theorem extreme_point_correspondence {n : ℕ} (r1 r2 : Finset (Fin n) → ℝ) (pi : Fin n → ℝ)
    (hpi : pi ∈ Set.extremePoints ℝ (PiSet r1 r2)) :
    ∃ u ∈ Set.extremePoints ℝ (USet r1 r2),
      ∀ j, pi j = ∑ A ∈ Finset.univ.filter (fun A => j ∈ A), u A := by sorry

end Disjunctive.Polymatroids

