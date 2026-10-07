import Mathlib

namespace DeterioratingJobs.Makespan

/-- The sum (1) of Lemma 1 (Browne–Yechiali 1990, p. 495), evaluated along the permutation `π`:
`∑_{i} μ_{π(i)} ∏_{r > i} γ_{π(r)}`. Positions are 0-based: `π i` is the job in position `i`, and
the product runs over the positions strictly after `i` (empty product `= 1` at the last position). -/
noncomputable def lemma1Sum {N : ℕ} (μ γ : Fin N → ℝ) (π : Equiv.Perm (Fin N)) : ℝ :=
  ∑ i : Fin N, μ (π i) * ∏ r ∈ Finset.Ioi i, γ (π r)

end DeterioratingJobs.Makespan
