import Definitions.Def_LeightonRao_Uniform_Dual

set_option autoImplicit false
open scoped BigOperators

namespace LeightonRao.Uniform

/-- Lemma 3, p. 797: a bounded-radius partition with controlled crossing capacity. -/
theorem lemma_3 {V : Type} [Fintype V] [DecidableEq V]
    (N : Network V) (d : V → V → ℝ) (hd : IsDistanceFunction d)
    (Δ : ℝ) (hΔ : 0 < Δ) :
    ∃ P : Finpartition (Finset.univ : Finset V),
      (∀ S ∈ P.parts, HasRadiusLE N d S Δ) ∧
      crossCap N P ≤ 4 * totalWeight N d * Real.logb 2 (Fintype.card V : ℝ) / Δ := by sorry

end LeightonRao.Uniform

