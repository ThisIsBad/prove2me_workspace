import Mathlib
import Definitions.Def_OceanicGames_Interior_Basic
open MeasureTheory Filter Topology

namespace OceanicGames.Interior

/-- Lemma, (4.11)–(4.13), pp. 14–15: the value of an added major player `m+1` of weight `w'` in
`Γ⁺(z)` is `(1/α) ∫_{t_1}^{t_2} Φ(y) dy`, `t_1 = max (z − w', 0)`, `t_2 = min (z, w(M) + α)`, for
`0 ≤ z ≤ w(M) + w' + α`; under (4.10) `w' ≤ z ≤ w(M) + α` it is `(1/α) ∫_{z−w'}^{z} Φ(y) dy`. -/
theorem lemma_4_12 {m : ℕ} (α w' : ℝ) (w : Fin m → ℝ) (hα : 0 < α) (hw : ∀ j, 0 ≤ w j)
    (hw' : 0 ≤ w') (z : ℝ) (hz0 : 0 ≤ z) (hzW : z ≤ wsum w Finset.univ + w' + α) :
    value z α (addWeight w w') (Fin.last m) =
        1 / α * ∫ y in (max (z - w') 0)..(min z (wsum w Finset.univ + α)), oceanValue y α w ∧
    (w' ≤ z → z ≤ wsum w Finset.univ + α →
      value z α (addWeight w w') (Fin.last m) =
        1 / α * ∫ y in (z - w')..z, oceanValue y α w) := by sorry

end OceanicGames.Interior

