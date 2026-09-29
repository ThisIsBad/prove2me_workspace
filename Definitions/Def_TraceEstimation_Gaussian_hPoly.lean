import Mathlib

namespace TraceEstimation.Gaussian

/-- The higher-order part `h(t)` of the moment generating function in Section 5, Eq. (1)
(Avron–Toledo, pp. 8:7–8:8): for a list of eigenvalues `λ_1, …, λ_n` (with multiplicity),
`h(t) = ∑_{s=2}^n (-2)^s t^s ∑_{S ⊆ [n], |S| = s} ∏_{i ∈ S} λ_i`. -/
noncomputable def hPoly {n : ℕ} (lam : Fin n → ℝ) (t : ℝ) : ℝ :=
  ∑ s ∈ Finset.Icc 2 n, (-2 : ℝ) ^ s * t ^ s *
    ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard s, ∏ i ∈ S, lam i

end TraceEstimation.Gaussian
