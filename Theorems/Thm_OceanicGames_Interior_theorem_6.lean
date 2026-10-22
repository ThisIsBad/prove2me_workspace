import Mathlib
import Definitions.Def_OceanicGames_Interior_Basic
open MeasureTheory Filter Topology

namespace OceanicGames.Interior

/-- Theorem 6, (5.9)–(5.10), p. 20: in the interior oceanic game `[c; w_1, …, w_m; α]`,
`w(M) ≤ c ≤ α`, `φ_i = (w_i/α) Σ_{S⊆M−{i}} a_s π_i(S)` and `Φ = Σ_{S⊆M} a_s π(S)`. -/
theorem theorem_6 {m : ℕ} (c α : ℝ) (w : Fin m → ℝ) (hα : 0 < α) (hw : ∀ j, 0 ≤ w j)
    (hint : IsInterior c α w) :
    (∀ i, value c α w i =
      w i / α * ∑ S ∈ (Finset.univ.erase i).powerset, (coeff S.card : ℝ) * piProdErase α w i S) ∧
    oceanValue c α w =
      ∑ S ∈ (Finset.univ : Finset (Fin m)).powerset, (coeff S.card : ℝ) * piProd α w S := by sorry

end OceanicGames.Interior

