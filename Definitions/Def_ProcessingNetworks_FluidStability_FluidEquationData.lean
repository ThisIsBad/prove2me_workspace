import Mathlib

namespace ProcessingNetworks.FluidStability

/-- Fluid-equation model data for an SPN, Dai & Harrison, Section 2.1/2.5 recap and Section 6.1:
`I` buffers, `J` activities, `K` server pools. `B`, `Γ` are the `I × J` material-requirement
matrix (2.9) and expected-output matrix (Assumption 2.1(b)/(2.13)); `m` is the vector of mean
service times (so `M := diag(m)` of Section 2.6, and (6.4)'s `F̂ = M⁻¹T̂` is stated directly as
`m j * F̂ j = T̂ j`, avoiding a matrix inverse); `A`, `b` are the `K × J` capacity-consumption
matrix and `K`-vector of server-pool capacities of (2.11)/(5.2); `lam` is the vector of external
arrival rates of Assumption 2.1(a). -/
structure FluidEquationData (I J K : ℕ) where
  B : Matrix (Fin I) (Fin J) ℝ
  Γ : Matrix (Fin I) (Fin J) ℝ
  m : Fin J → ℝ
  A : Matrix (Fin K) (Fin J) ℝ
  b : Fin K → ℝ
  lam : Fin I → ℝ

/-- The fluid equations (6.1)-(6.6), Dai & Harrison p. 106 (PDF p. 122): a four-tuple
`(D̂, F̂, T̂, Ẑ)` of functions on `ℝ` (only `t ≥ 0` is meaningful) is a *fluid model solution* for
the data `dat` if, for every `t ≥ 0`: the buffer-content balance (6.1) holds; `Ẑ(t) ≥ 0`
componentwise (6.2); the departure/completion relationship `D̂ = B F̂` holds (6.3); the
completion/effort relationship `m_j F̂_j(t) = T̂_j(t)` holds for every activity `j`, equivalent to
`F̂ = M⁻¹T̂` since every `m j > 0` (6.4); `T̂` is nondecreasing with `T̂(0) = 0` (6.5); and the
capacity/Lipschitz bound (6.6) holds for every `0 ≤ s ≤ t`. -/
def IsFluidModelSolution {I J K : ℕ} (dat : FluidEquationData I J K)
    (Dh : ℝ → Fin I → ℝ) (Fh Th : ℝ → Fin J → ℝ) (Zh : ℝ → Fin I → ℝ) : Prop :=
  (∀ t : ℝ, 0 ≤ t → ∀ i, Zh t i = Zh 0 i + dat.lam i * t + ∑ j, dat.Γ i j * Fh t j - Dh t i) ∧
  (∀ t : ℝ, 0 ≤ t → ∀ i, 0 ≤ Zh t i) ∧
  (∀ t : ℝ, 0 ≤ t → ∀ i, Dh t i = ∑ j, dat.B i j * Fh t j) ∧
  (∀ t : ℝ, 0 ≤ t → ∀ j, dat.m j * Fh t j = Th t j) ∧
  (Th 0 = 0 ∧ Monotone Th) ∧
  (∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ k, ∑ j, dat.A k j * (Th t j - Th s j) ≤ dat.b k * (t - s))

end ProcessingNetworks.FluidStability
