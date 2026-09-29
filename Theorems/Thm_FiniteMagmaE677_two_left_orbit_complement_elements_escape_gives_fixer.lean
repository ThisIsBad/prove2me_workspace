import Definitions.Def_FiniteMagmaE677

universe u

theorem FiniteMagmaE677.two_left_orbit_complement_elements_escape_gives_fixer
    {α : Type u} [Fintype α] (op : α → α → α) (h : FiniteMagmaE677.E677 op)
    (x : α) (hni : op x x ≠ x)
    (htwo : ∃ a b : α,
      a ≠ b ∧
        ¬ FiniteMagmaE677.InLeftOrbit op x a ∧
          ¬ FiniteMagmaE677.InLeftOrbit op x b)
    (hescape : ∃ a : α,
      FiniteMagmaE677.InLeftOrbit op x a ∧
        ¬ FiniteMagmaE677.InLeftOrbit op x (op a x)) :
    FiniteMagmaE677.HasFixerAt op x := by sorry
