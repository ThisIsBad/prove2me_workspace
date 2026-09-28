import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto

namespace SpectralProjGrad.SPG1

/-- Lemma 2.2 (i): for `x ∈ Ω` and `z ∈ ℝⁿ`, the function `h(s) = ‖P(x + s z) - x‖ / s` is
monotonically nonincreasing on `s > 0` (the only values at which the paper defines it). -/
theorem projection_ratio_antitone {n : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hΩ_closed : IsClosed Ω) (hΩ_convex : Convex ℝ Ω)
    (hP : SpectralProjGrad.Shared.IsProjOnto Ω P)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Ω) (z : EuclideanSpace ℝ (Fin n)) :
    AntitoneOn (fun s : ℝ => ‖P (x + s • z) - x‖ / s) (Set.Ioi 0) := by sorry

end SpectralProjGrad.SPG1

