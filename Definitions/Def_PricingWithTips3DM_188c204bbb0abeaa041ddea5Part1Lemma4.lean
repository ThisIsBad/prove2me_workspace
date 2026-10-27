import Definitions.Def_PricingWithTips3DM_8fb65f62dc7f7936c2bf07db
import Mathlib.Tactic
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CLRS.Chapter34.Turing.TMClique
open PolyBuilder

theorem sum_map_le_mul {α : Type} (xs : List α) (f : α → Nat)
    (bound : Nat) (hbound : ∀ x ∈ xs, f x ≤ bound) :
    (xs.map f).sum ≤ xs.length * bound := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx := hbound x (by simp)
      have htail : ∀ y ∈ xs, f y ≤ bound := by
        intro y hy
        exact hbound y (by simp [hy])
      have hrest := ih htail
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      nlinarith
end CLRS.Chapter34.Turing.TMClique
