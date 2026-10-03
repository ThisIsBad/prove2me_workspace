import Mathlib

namespace ProcessingNetworks.TaskAllocation

/-- The task allocation model's data (Sections 11.2-11.3): `L` categories, `K` servers, mean
service times `m ℓ k` for a class-`(ℓ,k)` task (Eq. 11.3, all strictly positive), and the
Markovian-arrival-process long-run average arrival rate vector `ν` (Section 11.4, `ν ≥ 0`). Class
`(ℓ,k)` is represented directly as the pair `(ℓ,k) : Fin L × Fin K` throughout this mission,
rather than flattened to a single `Fin I` with `I = LK` (Section 11.3): the two representations
are in bijection, and using the pair directly avoids an arbitrary encoding of the bijection. -/
structure TaskAllocationData (L K : ℕ) where
  m : Fin L → Fin K → ℝ
  hm : ∀ ℓ k, 0 < m ℓ k
  nu : Fin L → ℝ
  hnu : ∀ ℓ, 0 ≤ nu ℓ

/-- The task allocation model is subcritical (last paragraph of Section 5.2, restated locally per
this chunk's own `BRIEF.md`: mission II's general SPN subcriticality is not imported), in the
general form (11.6) that Lemma 11.2's proof derives for this model's own source-buffer matrix `G`
(`Gℓ,(ℓ,k) = 1`), input-output matrix `R = M⁻¹` (since `Γ = 0`, `B = I`), capacity-consumption
matrix `A` (`Ak,(ℓ,k) = 1`), and capacities `b = 1` (Eq. 11.1): there exist `λ ≥ 0` with `Gλ = ν`
and `x ≥ 0` with `Rx = λ` (i.e. `x = Mλ`, substituted directly here) and `Ax < b`. -/
def IsSubcriticalGeneral {L K : ℕ} (dat : TaskAllocationData L K) : Prop :=
  ∃ (lam x : Fin L → Fin K → ℝ),
    (∀ ℓ k, 0 ≤ lam ℓ k) ∧ (∀ ℓ k, 0 ≤ x ℓ k) ∧
    (∀ ℓ, ∑ k, lam ℓ k = dat.nu ℓ) ∧
    (∀ ℓ k, x ℓ k = dat.m ℓ k * lam ℓ k) ∧
    (∀ k, ∑ ℓ, x ℓ k < 1)

end ProcessingNetworks.TaskAllocation
