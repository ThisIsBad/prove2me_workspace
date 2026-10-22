import Mathlib
import Definitions.Def_LeightonRao_Product_Setting

namespace LeightonRao.Product

theorem lemma_8 {V : Type} [Fintype V] [DecidableEq V] (N : Network V) (d : V → V → ℝ)
    (hd : IsDistanceFunction d) (π : V → ℝ) (hp : 2 ≤ (support π).card) (Δ : ℝ) (hΔ : 0 < Δ) :
    ∃ P : Finpartition (Finset.univ : Finset V),
      (∀ S ∈ P.parts, (∃ x ∈ S, π x ≠ 0) → HasRadiusLE N d S Δ) ∧
      crossCap N P ≤ 4 * totalWeight N d * Real.logb 2 ((support π).card : ℝ) / Δ := by sorry

end LeightonRao.Product

