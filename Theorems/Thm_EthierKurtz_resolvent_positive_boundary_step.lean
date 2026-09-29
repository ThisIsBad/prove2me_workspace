import Mathlib
import Definitions.Def_EthierKurtz_BoundaryCTwiceHolder
import Definitions.Def_EthierKurtz_IsOutwardUnitNormal

open Filter
open scoped Topology BoundedContinuousFunction

namespace EthierKurtz

theorem resolvent_positive_boundary_step {n : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} {μ : ℝ}
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {b c normal : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    {u g : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {x₀ : EuclideanSpace ℝ (Fin (n + 1))}
    {J0 : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ} {lam : ℝ}
    (hx : x₀ ∈ frontier Ω)
    (hboundary : BoundaryCTwiceHolder Ω μ) (hμ : 0 < μ ∧ μ ≤ 1)
    (hC : ContDiffOn ℝ 2 u Ω)
    (hcont : ContinuousOn u (closure Ω))
    (hcontG : ContinuousOn g (closure Ω))
    (hD : HasFDerivAt u J0 x₀)
    (hJ0b : J0 (c x₀) = 0)
    (hnor : IsOutwardUnitNormal Ω x₀ (normal x₀))
    (hob : ∃ ε : ℝ, 0 < ε ∧ ε ≤ ∑ i, c x₀ i * normal x₀ i)
    (hIdΩ : ∀ x ∈ Ω, g x = (1 / 2 : ℝ) * (∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
      a x i j * fderiv ℝ (fun y => fderiv ℝ u y (EuclideanSpace.single j 1)) x
        (EuclideanSpace.single i 1)) + fderiv ℝ u x (b x))
    (ha : ∀ x ∈ Ω, (a x).PosSemidef)
    (hell : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ Ω,
      ∀ θ : EuclideanSpace ℝ (Fin (n + 1)), ‖θ‖ = 1 →
        ε ≤ ∑ i, ∑ j, θ i * a x i j * θ j)
    (hminglob : ∀ y ∈ closure Ω, u x₀ ≤ u y)
    (hu0 : u x₀ < 0)
    (hlam : 0 < lam)
    (hop : 0 ≤ lam * u x₀ - g x₀) :
    False := by sorry

end EthierKurtz
