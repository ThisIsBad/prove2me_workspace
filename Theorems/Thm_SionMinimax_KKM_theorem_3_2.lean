import Mathlib

namespace SionMinimax.KKM
theorem theorem_3_2 {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (n : ℕ) (hdim : Module.finrank ℝ V < n)
    (a : Fin (n + 1) → V) (ha : Function.Injective a) :
    (⋂ i : Fin (n + 1), convexHull ℝ (Set.range a \ {a i})).Nonempty := by sorry
end SionMinimax.KKM

