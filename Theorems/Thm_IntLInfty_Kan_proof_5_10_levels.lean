import Mathlib
import Definitions.Def_IntLInfty_Kan_CE
import Definitions.Def_IntLInfty_Kan_Forms
import Definitions.Def_IntLInfty_Kan_Manifold
import Definitions.Def_IntLInfty_Kan_Integ

namespace IntLInfty.Kan

theorem proof_5_10_levels (r : ℕ) (hr : 1 ≤ r) (L : ℕ → Type) [∀ i, AddCommGroup (L i)]
    [∀ i, Module ℝ (L i)] [∀ i, FiniteDimensional ℝ (L i)] (δ : LInfty L) (m n : ℕ) (hmn : m ≤ n) :
    Set.BijOn (res (S := ⊤) (S' := tauLt δ n) (fun i => le_top) (r := r) (m := m))
      (integ r δ ⊤ m) (integ r δ (tauLt δ n) m) := by sorry

end IntLInfty.Kan

