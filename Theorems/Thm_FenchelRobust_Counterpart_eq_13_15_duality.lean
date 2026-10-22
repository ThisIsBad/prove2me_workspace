import Mathlib
import Definitions.Def_FenchelRobust_Counterpart_Model

namespace FenchelRobust.Counterpart

/-- Equations (13)–(15), including the attainment indicated by `min`. -/
theorem eq_13_15_duality {m n L : ℕ} (a0 : Fin m → ℝ)
    (A : Matrix (Fin m) (Fin L) ℝ) (Z : Set (Fin L → ℝ))
    (D : (Fin n → ℝ) → Set (Fin m → ℝ))
    (f : (Fin m → ℝ) → (Fin n → ℝ) → ℝ)
    (hZnonempty : Z.Nonempty) (hZconvex : Convex ℝ Z) (hZcompact : IsCompact Z)
    (hZzero : (0 : Fin L → ℝ) ∈ intrinsicInterior ℝ Z)
    (hconcave : ∀ x, ConcaveOn ℝ (D x) (fun a => f a x))
    (hregular : Regular a0 D) :
    ∀ x : Fin n → ℝ,
      let F := worstCase a0 A Z D f x
      let dual := fun v : Fin m → ℝ =>
        supportFun (uncertaintySet a0 A Z) v - concaveConj (D x) (fun a => f a x) v
      F = (⨅ v, dual v) ∧ ∃ v, F = dual v := by sorry

end FenchelRobust.Counterpart

