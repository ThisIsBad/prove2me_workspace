import Definitions.Def_auto_GRU_M05_GALE_EQ_IsDPolytope
import Definitions.Def_auto_GRU_M05_GALE_EQ_PolytopeFace
import Definitions.Def_auto_GRU_M05_GALE_EQ_IsGaleTransform

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

theorem auto_GRU_M05_GALE_EQ_gale_combinatorial_equivalence (d n : ℕ)
    (P Q : Set (Fin d → ℝ)) (hP : IsDPolytope P) (hQ : IsDPolytope Q)
    (V W : Fin n → (Fin d → ℝ))
    (hVinj : Function.Injective V) (hWinj : Function.Injective W)
    (hV : Set.range V = {x | IsExposed ℝ P {x}})
    (hW : Set.range W = {x | IsExposed ℝ Q {x}})
    (G H : Fin n → (Fin (n - d - 1) → ℝ))
    (hG : IsGaleTransform V G) (hH : IsGaleTransform W H)
    (θ : Equiv.Perm (Fin n)) :
    (∃ Φ : PolytopeFace P ≃o PolytopeFace Q,
      ∀ (i : Fin n) (F : PolytopeFace P),
        F.val = {V i} → (Φ F).val = {W (θ i)}) ↔
    (∀ J : Set (Fin n),
      (0 : Fin (n - d - 1) → ℝ) ∈ intrinsicInterior ℝ (convexHull ℝ (G '' J)) ↔
      (0 : Fin (n - d - 1) → ℝ) ∈
        intrinsicInterior ℝ (convexHull ℝ (H '' (θ '' J)))) := by sorry

end Grunbaum2003
