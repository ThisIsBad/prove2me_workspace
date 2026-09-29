import Definitions.Def_FiniteMagmaE677

universe u

theorem FiniteMagmaE677.cross_boundary_collision_propagates_to_left_successor
    {α : Type u} [Fintype α] (op : α → α → α) (h : FiniteMagmaE677.E677 op)
    (x A : α)
    (hnofix : ¬ FiniteMagmaE677.HasFixerAt op x)
    (hA_notin : ¬ FiniteMagmaE677.InLeftOrbit op x A)
    (hA_unique : ∀ a : α, ¬ FiniteMagmaE677.InLeftOrbit op x a → a = A)
    (c : α) (hc : FiniteMagmaE677.InLeftOrbit op x c)
    (hcollision : op c x = op A x) :
    op (op x c) x = op A x := by sorry
