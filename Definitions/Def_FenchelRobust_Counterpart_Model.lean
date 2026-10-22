import Mathlib
import Definitions.Def_FenchelRobust_Counterpart_ConvexDuality

namespace FenchelRobust.Counterpart

/-- The affine uncertainty set of Section 2. -/
def uncertaintySet {m L : ℕ} (a0 : Fin m → ℝ)
    (A : Matrix (Fin m) (Fin L) ℝ) (Z : Set (Fin L → ℝ)) : Set (Fin m → ℝ) :=
  {a | ∃ ζ ∈ Z, a = a0 + Matrix.mulVec A ζ}

/-- Definition 1: the nominal vector is regular for every decision. -/
def Regular {m n : ℕ} (a0 : Fin m → ℝ)
    (D : (Fin n → ℝ) → Set (Fin m → ℝ)) : Prop :=
  ∀ x, a0 ∈ intrinsicInterior ℝ (D x)

/-- The robust constraint (6), with values outside the effective domain interpreted as `-∞`. -/
def RobustFeasible {m n L : ℕ} (a0 : Fin m → ℝ)
    (A : Matrix (Fin m) (Fin L) ℝ) (Z : Set (Fin L → ℝ))
    (D : (Fin n → ℝ) → Set (Fin m → ℝ))
    (f : (Fin m → ℝ) → (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : Prop :=
  ∀ a ∈ uncertaintySet a0 A Z, a ∈ D x → f a x ≤ 0

/-- The extended-real worst-case value in (8) and (13). -/
noncomputable def worstCase {m n L : ℕ} (a0 : Fin m → ℝ)
    (A : Matrix (Fin m) (Fin L) ℝ) (Z : Set (Fin L → ℝ))
    (D : (Fin n → ℝ) → Set (Fin m → ℝ))
    (f : (Fin m → ℝ) → (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : EReal :=
  ⨆ a ∈ uncertaintySet a0 A Z ∩ D x, (f a x : EReal)

/-- The extended-real left side of the Fenchel robust counterpart (12). -/
noncomputable def frcValue {m n L : ℕ} (a0 : Fin m → ℝ)
    (A : Matrix (Fin m) (Fin L) ℝ) (Z : Set (Fin L → ℝ))
    (D : (Fin n → ℝ) → Set (Fin m → ℝ))
    (f : (Fin m → ℝ) → (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) (v : Fin m → ℝ) : EReal :=
  ((a0 ⬝ᵥ v : ℝ) : EReal) + supportFun Z (Matrix.mulVec A.transpose v) -
    concaveConj (D x) (fun a => f a x) v

end FenchelRobust.Counterpart
