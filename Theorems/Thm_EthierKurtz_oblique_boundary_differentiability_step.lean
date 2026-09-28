import Mathlib

open scoped Topology

namespace EthierKurtz

theorem oblique_boundary_differentiability_step {d : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {x₀ : EuclideanSpace ℝ (Fin d)}
    {J : (closure Ω) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)}
    (hx : x₀ ∈ frontier Ω) (hxmem : x₀ ∈ closure Ω)
    (hC : ContDiffOn ℝ 2 u Ω)
    (hcont : ContinuousOn u (closure Ω))
    (hJc : Continuous J)
    (hJid : ∀ x : (closure Ω), (x : EuclideanSpace ℝ (Fin d)) ∈ Ω →
      J x = fderiv ℝ u x) :
    HasFDerivAt u (J ⟨x₀, hxmem⟩) x₀ := by sorry

end EthierKurtz
