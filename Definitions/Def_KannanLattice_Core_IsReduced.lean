import Mathlib
import Definitions.Def_KannanLattice_Core_Lattice

namespace KannanLattice.Core

/-- A reduced basis in the sense of Definition 2.6 (Kannan 1987, p. 11), i.e. a
Korkine–Zolotarev basis. With 0-based indices:

* (2.7) for every `j`, `b_j(j) = Λ₁(L_j(b))`: the `j`-th Gram–Schmidt length is the length of a
  shortest nonzero vector of the projected lattice;
* (2.8) for `i > j`, `|b_i(j)| ≤ b_j(j)/2`. -/
def IsReduced {m k : ℕ} (b : Fin m → EuclideanSpace ℝ (Fin k)) : Prop :=
  (∀ j : Fin m, gsLen b j = lambdaOne (projLattice b j)) ∧
  (∀ i j : Fin m, j < i → |gsCoeff b i j| ≤ gsLen b j / 2)

end KannanLattice.Core
