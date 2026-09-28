import Mathlib

namespace MonotonicSolutions.StrongMono

/-- The primitive (unanimity) game `v_R` of Young (1985, p. 70, Eq. (9)): `v_R(S) = 1` if
`R ⊆ S` and `0` otherwise. In Eq. (9) it is used only for nonempty `R`. -/
def unanimity {n : ℕ} (R S : Finset (Fin n)) : ℝ := if R ⊆ S then 1 else 0

end MonotonicSolutions.StrongMono
