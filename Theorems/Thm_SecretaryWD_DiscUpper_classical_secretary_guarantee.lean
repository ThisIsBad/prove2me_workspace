import Mathlib
import Definitions.Def_SecretaryWD_DiscUpper_ClassicalSecretary

namespace SecretaryWD.DiscUpper
theorem classical_secretary_guarantee (m : ℕ) (hm : 1 ≤ m) (v : Fin m → ℝ) :
    1 / Real.exp 1 ≤
      (1 / (m.factorial : ℝ)) *
        ((Finset.univ.filter fun σ : Equiv.Perm (Fin m) =>
            ∃ t : Fin m, classicalSecretary m (fun s => tieKey v (σ s)) = some t ∧
              ∀ e : Fin m, tieKey v e ≤ tieKey v (σ t)).card : ℝ) := by sorry
end SecretaryWD.DiscUpper

