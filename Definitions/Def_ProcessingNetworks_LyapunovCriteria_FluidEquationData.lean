import Mathlib

namespace ProcessingNetworks.LyapunovCriteria

/-- Fluid-equation model data, restated from mission III's `FluidEquationData` (drafts in this
series do not import one another): `I` buffers, `J` activities, `K` server pools, the `I × J`
material-requirement matrix `B` and expected-output matrix `Γ`, the vector `m` of mean service
times, the `K × J` capacity-consumption matrix `A` and `K`-vector `b` of server-pool capacities,
and the vector `lam` of external arrival rates. -/
structure FluidEquationData (I J K : ℕ) where
  B : Matrix (Fin I) (Fin J) ℝ
  Γ : Matrix (Fin I) (Fin J) ℝ
  m : Fin J → ℝ
  A : Matrix (Fin K) (Fin J) ℝ
  b : Fin K → ℝ
  lam : Fin I → ℝ

/-- The fluid equations (6.1)-(6.6), restated from mission III's `IsFluidModelSolution` (see that
mission's `MODERATION_NOTES.md` for the per-conjunct correspondence to (6.1)-(6.6)). -/
def IsFluidModelSolution {I J K : ℕ} (dat : FluidEquationData I J K)
    (Dh : ℝ → Fin I → ℝ) (Fh Th : ℝ → Fin J → ℝ) (Zh : ℝ → Fin I → ℝ) : Prop :=
  (∀ t : ℝ, 0 ≤ t → ∀ i, Zh t i = Zh 0 i + dat.lam i * t + ∑ j, dat.Γ i j * Fh t j - Dh t i) ∧
  (∀ t : ℝ, 0 ≤ t → ∀ i, 0 ≤ Zh t i) ∧
  (∀ t : ℝ, 0 ≤ t → ∀ i, Dh t i = ∑ j, dat.B i j * Fh t j) ∧
  (∀ t : ℝ, 0 ≤ t → ∀ j, dat.m j * Fh t j = Th t j) ∧
  (Th 0 = 0 ∧ Monotone Th) ∧
  (∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ k, ∑ j, dat.A k j * (Th t j - Th s j) ≤ dat.b k * (t - s))

end ProcessingNetworks.LyapunovCriteria
