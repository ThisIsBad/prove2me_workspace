import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators

open InnerProductSpace

namespace DouglasRachfordPPA.GenDR

/-! Operators on `H` are subsets of `H × H`, encoded as `T : H → Set H` with graph
`{(x, y) | y ∈ T x}` (Eckstein–Bertsekas, pp. 3–5). Monotonicity, maximality, `dom` and `zer`
are the published `ThreeOpSplitting.Convergence` notions. -/

/-- The identity operator `I = {(x, x) | x ∈ H}`. -/
def opId {H : Type*} : H → Set H := fun x => {x}

/-- The scaled operator `cT = {(x, c y) | (x, y) ∈ T}`. -/
def opSmul {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (c : ℝ) (T : H → Set H) : H → Set H :=
  fun x => {w | ∃ y ∈ T x, w = c • y}

/-- The sum `A + B = {(x, y + z) | (x, y) ∈ A, (x, z) ∈ B}`; its domain is `dom A ∩ dom B`. -/
def opAdd {H : Type*} [Add H] (A B : H → Set H) : H → Set H :=
  fun x => {w | ∃ y ∈ A x, ∃ z ∈ B x, w = y + z}

/-- The inverse `T⁻¹ = {(y, x) | (x, y) ∈ T}`. -/
def opInv {H : Type*} (T : H → Set H) : H → Set H := fun y => {x | y ∈ T x}

/-- The image (range) `im T = {y | ∃ x, (x, y) ∈ T}`. -/
def imOp {H : Type*} (T : H → Set H) : Set H := {y | ∃ x, y ∈ T x}

/-- The resolvent `J_{cT} = (I + cT)⁻¹`, as an operator (a graph, possibly multivalued and
not everywhere defined). -/
def opResolvent {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (c : ℝ) (T : H → Set H) : H → Set H :=
  opInv (opAdd opId (opSmul c T))

/-- An operator `T` is single-valued if `T x` has at most one element for every `x`. -/
def IsSingleValuedOp {H : Type*} (T : H → Set H) : Prop :=
  ∀ x y y' : H, y ∈ T x → y' ∈ T x → y = y'

/-- An operator `C` is nonexpansive if `‖y' - y‖ ≤ ‖x' - x‖` for all `(x, y), (x', y') ∈ C`. -/
def IsNonexpansiveOp {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (C : H → Set H) : Prop :=
  ∀ x x' y y' : H, y ∈ C x → y' ∈ C x' → ‖y' - y‖ ≤ ‖x' - x‖

/-- An operator `J` is firmly nonexpansive if `‖y' - y‖² ≤ ⟪x' - x, y' - y⟫` for all
`(x, y), (x', y') ∈ J`. -/
def IsFirmlyNonexpansiveOp {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (J : H → Set H) : Prop :=
  ∀ x x' y y' : H, y ∈ J x → y' ∈ J x' → ‖y' - y‖ ^ 2 ≤ ⟪x' - x, y' - y⟫_ℝ

end DouglasRachfordPPA.GenDR
