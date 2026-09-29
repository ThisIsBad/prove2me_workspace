import Definitions.Def_EthierKurtz_CTwiceHolder

open Filter
open scoped Topology BoundedContinuousFunction

namespace EthierKurtz

/-- The source's uniform-radius orthogonal graph charts. Zero derivative
at the chart origin identifies the last axis as normal. Its sign is irrelevant
to this boundary regularity predicate (and may be chosen outward). -/
def BoundaryCTwiceHolder {n : ℕ}
    (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))) (μ : ℝ) : Prop :=
  ∃ ρ : ℝ, 0 < ρ ∧ ∀ x₀ ∈ frontier Ω,
    ∃ U : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ]
        EuclideanSpace ℝ (Fin (n + 1)),
    ∃ D : Set (EuclideanSpace ℝ (Fin n)),
    ∃ u : EuclideanSpace ℝ (Fin n) → ℝ,
      IsOpen D ∧ (0 : EuclideanSpace ℝ (Fin n)) ∈ D ∧
      CTwiceHolder D μ u ∧ u 0 = 0 ∧ fderiv ℝ u 0 = 0 ∧
      IsConnected (frontier Ω ∩ Metric.ball x₀ ρ) ∧
      (fun x => U (x - x₀)) '' (frontier Ω ∩ Metric.ball x₀ ρ) =
        (fun z : EuclideanSpace ℝ (Fin n) =>
          (WithLp.toLp 2 (Fin.lastCases (u z) (fun i => z i)) :
            EuclideanSpace ℝ (Fin (n + 1)))) '' D

end EthierKurtz
