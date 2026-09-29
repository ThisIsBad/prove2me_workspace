import Mathlib
import Definitions.Def_EdmondsKarp_MaxCapacity_Network
import Definitions.Def_EdmondsKarp_MaxCapacity_Augmentation

namespace EdmondsKarp.MaxCapacity

/-- §1.1, p. 250: if all capacities are integers, then for any augmenting path `P` relative to any
integer-valued flow `f`, `ε` is a positive integer, and the augmented flow is again integer-valued. -/
theorem augment_integral {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (hcap : IntegralCaps N) (f : V → V → ℝ) (P : List V) (hf : IsFlow N f)
    (hfint : IsIntegralOn N f) (hP : IsAugPath N f P) :
    (∃ z : ℤ, 0 < z ∧ pathEps N f P = z) ∧ IsIntegralOn N (augment N f P) := by sorry

end EdmondsKarp.MaxCapacity
