import Mathlib

namespace FoundationsRL.Bandits

/-- The number of times decision `a` has been selected strictly before round `t`,
`n_t(π) := |{s < t : π_s = π}|` (Foster–Rakhlin, p. 23, following Eq. (2.5)),
for a realized decision sequence `pi : ℕ → Fin A`. -/
def pullCount {A : ℕ} (pi : ℕ → Fin A) (t : ℕ) (a : Fin A) : ℕ :=
  ((Finset.range t).filter (fun s => pi s = a)).card

end FoundationsRL.Bandits
