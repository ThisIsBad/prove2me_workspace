import Definitions.Def_EthierKurtz_CTwiceHolder
import Definitions.Def_EthierKurtz_COnceHolder

open Filter
open scoped Topology BoundedContinuousFunction

namespace EthierKurtz

/-- C^{1,μ} boundary functions in the orthogonal graph coordinates of p. 368.
The sign of the last coordinate is immaterial for this regularity predicate.
The ambient function is used only on the frontier. -/
def BoundaryCOnceHolder {n : ℕ}
    (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))) (μ : ℝ)
    (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) : Prop :=
  ∀ x₀ ∈ frontier Ω, ∃ ρ : ℝ, 0 < ρ ∧
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
            EuclideanSpace ℝ (Fin (n + 1)))) '' D ∧
      COnceHolder D μ (fun z => φ (x₀ + U.symm
        (WithLp.toLp 2 (Fin.lastCases (u z) (fun i => z i)))))

end EthierKurtz
