import Mathlib.Data.Fintype.Basic

/-! The operation is arbitrary: no associativity, identity, or cancellation is assumed. -/
namespace FiniteMagmaE677

universe u

def E677 {α : Type u} (op : α → α → α) : Prop :=
  ∀ x y : α, x = op y (op x (op (op y x) y))

def E255 {α : Type u} (op : α → α → α) : Prop :=
  ∀ x : α, x = op (op (op x x) x) x

/-- An element whose right product with `x` is `x`. -/
def HasFixerAt {α : Type u} (op : α → α → α) (x : α) : Prop :=
  ∃ y : α, op y x = x

/-- Membership in the forward orbit of `x` under left multiplication by `x`. -/
def InLeftOrbit {α : Type u} (op : α → α → α) (x a : α) : Prop :=
  ∃ i : ℕ, a = (op x)^[i] x

/-- A collision of right products on the left orbit of `x` either is trivial or yields a fixer. -/
def OrbitRightCollisionOrFixer {α : Type u} (op : α → α → α) (x : α) : Prop :=
  ∀ ⦃a b : α⦄,
    InLeftOrbit op x a →
    InLeftOrbit op x b →
    op a x = op b x →
    a = b ∨ HasFixerAt op x

end FiniteMagmaE677
