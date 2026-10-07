import Mathlib
import Definitions.Def_ManneJobShop_Formulation_Model

namespace ManneJobShop.Formulation

/-- Manne (1960), pp. 221–222: if every one of the `M` machines carries exactly `p` tasks, then
there are `n = M p` tasks and `m = M · p(p - 1)/2` conflicting pairs, i.e. `n + m` unknowns
`x_j, y_jk` (for 5 machines and 10 tasks each: 50 + 225 = 275). -/
theorem card_conflicts_uniform {n : ℕ} (I : Instance n) (p : ℕ)
    (hp : ∀ i : Fin I.M, (Finset.univ.filter (fun j : Fin n => I.mach j = i)).card = p) :
    n = I.M * p ∧ (conflicts I).card = I.M * (p * (p - 1) / 2) := by sorry

end ManneJobShop.Formulation

