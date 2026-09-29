import Mathlib
import Definitions.Def_CaiCandesShen_ProximalLimit_Basic
import Definitions.Def_CaiCandesShen_ProximalLimit_Problems
open Filter Topology

namespace CaiCandesShen.ProximalLimit

/-- Proof of Theorem 3.1, p. 1967, last line ("since X_∞ is unique"): when the `f_i` are convex,
the minimum Frobenius norm solution (3.14) of (1.6) is unique. -/
theorem min_frobenius_solution_unique {m n₁ n₂ : ℕ} (f : Fin m → Mat n₁ n₂ → ℝ)
    (hconv : ∀ i, ConvexOn ℝ Set.univ (f i))
    (X X' : Mat n₁ n₂) (hX : IsMinFrobeniusSolution f X)
    (hX' : IsMinFrobeniusSolution f X') :
    X = X' := by sorry

end CaiCandesShen.ProximalLimit
