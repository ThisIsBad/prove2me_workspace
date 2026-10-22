import Mathlib
import Definitions.Def_OceanicGames_Interior_Basic
open MeasureTheory Filter Topology

namespace OceanicGames.Interior

/-- (4.4)–(4.5), p. 10: for `0 < y < w(M) + α`, `F(y)` is differentiable at `y` with
probability 1, `Σ φ_i(y) = Prob {F'(y) = 0}` and `Φ(y) = Prob {F'(y) = 1/α}`. -/
theorem eq_4_4_4_5 {m : ℕ} (α : ℝ) (w : Fin m → ℝ) (hα : 0 < α) (hw : ∀ j, 0 ≤ w j)
    (y : ℝ) (hy0 : 0 < y) (hyW : y < wsum w Finset.univ + α) :
    volume {x | x ∈ cube m ∧ ¬ DifferentiableAt ℝ (fun z => pivotLoc α w x z) y} = 0 ∧
    ∑ i, value y α w i =
      (volume {x | x ∈ cube m ∧ HasDerivAt (fun z => pivotLoc α w x z) 0 y}).toReal ∧
    oceanValue y α w =
      (volume {x | x ∈ cube m ∧ HasDerivAt (fun z => pivotLoc α w x z) (1 / α) y}).toReal := by sorry

end OceanicGames.Interior

