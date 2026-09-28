import Mathlib
import Definitions.Def_SPOBounds_Polyhedral_NegNormalCone

namespace SPOBounds.Polyhedral

theorem aux_nnc_convex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (chat : StrongDual ℝ E) (y : E) : Convex ℝ {x : E | 0 ≤ chat (x - y)} := by
  have h : {x : E | 0 ≤ chat (x - y)} = {x : E | chat y ≤ chat x} := by
    ext x; simp [map_sub, sub_nonneg]
  rw [h]
  exact convex_halfSpace_ge chat.isLinear (chat y)

end SPOBounds.Polyhedral

open SPOBounds.Polyhedral

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : ℕ} (v : Fin K → E) (hv : Function.Injective v)
    (S : Set E) (hS : S = convexHull ℝ (Set.range v)) (j : Fin K) :
    negNormalCone S (v j) = {chat : StrongDual ℝ E | ∀ i, 0 ≤ chat (v i - v j)} := by
  subst hS
  ext chat
  simp only [negNormalCone, Set.mem_ofPred_eq]
  constructor
  · intro h i
    exact h (v i) (subset_convexHull ℝ _ ⟨i, rfl⟩)
  · intro h x hx
    have hsub : Set.range v ⊆ {x : E | 0 ≤ chat (x - v j)} := by
      rintro _ ⟨i, rfl⟩
      exact h i
    exact (convexHull_min hsub (aux_nnc_convex chat (v j))) hx
