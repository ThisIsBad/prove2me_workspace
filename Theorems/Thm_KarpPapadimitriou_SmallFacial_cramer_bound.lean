import Mathlib
import Definitions.Def_KarpPapadimitriou_SmallFacial_COP

namespace KarpPapadimitriou.SmallFacial

/-- pp. 6–7, proof of Lemma 1: bounded integral normals from `n-1` independent rows. -/
theorem cramer_bound (n x : ℕ) (hn : 1 ≤ n) (hx : 1 ≤ x)
    (W : Matrix (Fin (n - 1)) (Fin n) ℤ) (v₀ : Fin n → ℤ)
    (hW : LinearIndependent ℚ (fun i : Fin (n - 1) => fun j : Fin n => (W i j : ℚ)))
    (hWb : ∀ i j, (W i j).natAbs ≤ 2 * x)
    (hv : ∀ j, (v₀ j).natAbs ≤ x) :
    ∃ f : Fin n → ℤ,
      f ≠ 0 ∧
      (∀ i, (∑ j, W i j * f j) = 0) ∧
      (∀ j, (f j).natAbs ≤ (2 * n * x) ^ n) ∧
      (∑ j, f j * v₀ j).natAbs ≤ (2 * n * x) ^ n := by sorry

end KarpPapadimitriou.SmallFacial

