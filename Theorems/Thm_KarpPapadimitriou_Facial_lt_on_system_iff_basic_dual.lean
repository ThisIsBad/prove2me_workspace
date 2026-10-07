import Mathlib
import Definitions.Def_KarpPapadimitriou_Facial_FacialDescription

namespace KarpPapadimitriou.Facial

theorem lt_on_system_iff_basic_dual (C : COP) (F : Triples C) (hF : IsFacialDescription C F)
    (hs : IsSmall C F) (z : List Bool) (hz : z ∈ C.L) (hS : (C.S z).Nonempty)
    (c : Fin (C.n z) → ℤ) (k : ℤ) :
    (∀ x : Fin (C.n z) → ℚ,
        (∀ (f : Fin (C.n z) → ℤ) (g : ℤ),
            (⟨z, (f, g)⟩ : Σ z : List Bool, (Fin (C.n z) → ℤ) × ℤ) ∈ F →
              (fun j => (f j : ℚ)) ⬝ᵥ x ≤ (g : ℚ)) →
          (fun j => (c j : ℚ)) ⬝ᵥ x < (k : ℚ)) ↔
      ∃ (fm : Matrix (Fin (C.n z)) (Fin (C.n z)) ℤ) (g : Fin (C.n z) → ℤ),
        (∀ i, (⟨z, (fm i, g i)⟩ : Σ z : List Bool, (Fin (C.n z) → ℤ) × ℤ) ∈ F) ∧
          fm.det ≠ 0 ∧
          ∃ y : Fin (C.n z) → ℚ,
            Matrix.vecMul y (fm.map (fun a : ℤ => (a : ℚ))) = (fun j => (c j : ℚ)) ∧
              0 ≤ y ∧ y ⬝ᵥ (fun i => (g i : ℚ)) < (k : ℚ) := by sorry

end KarpPapadimitriou.Facial

