import Mathlib
import Definitions.Def_StochApproxDyn_MartingaleNoise_Interpolation
import Definitions.Def_StochApproxDyn_MartingaleNoise_AssumptionA1
import Definitions.Def_StochApproxDyn_MartingaleNoise_RobbinsMonro

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace StochApproxDyn.MartingaleNoise

/-- Benaïm 1999, Proposition 4.2, p. 15: let `{x_n}` given by (7) be a Robbins–Monro algorithm.
Suppose that for some `q ≥ 2`, `sup_n E(‖U_{n+1}‖^q) < ∞` and `∑_n γ_n^{1+q/2} < ∞`. Then
assumption A1 holds with probability 1: for `P`-almost every `ω`, the realised noise
sequence satisfies A1 for every `T > 0` (in both of its stated forms). -/
theorem robbinsMonro_A1_ae {d : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (γ : ℕ → ℝ)
    (x U : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hRM : IsRobbinsMonro P ℱ F γ x U)
    (q : ℝ) (hq : 2 ≤ q)
    (hmom : ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ n : ℕ, ∫⁻ ω, ‖U (n + 1) ω‖ₑ ^ q ∂P ≤ M)
    (hsum : Summable (fun n : ℕ => γ (n + 1) ^ (1 + q / 2))) :
    ∀ᵐ ω ∂P, IsA1 γ (fun n => U n ω) ∧ IsA1Delta γ (fun n => U n ω) := by sorry

end StochApproxDyn.MartingaleNoise

