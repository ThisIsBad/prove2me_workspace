import Mathlib
import Definitions.Def_HighDimProb_Concentration_SubgaussianNorm

open MeasureTheory

namespace HighDimProb.Deviations

/-- The **sub-gaussian norm** `‖X‖_{ψ₂}` of a random vector `X : Ω → EuclideanSpace ℝ (Fin n)`.
Vershynin, *High-Dimensional Probability* (2018), Definition 3.4.1, p. 56 (PDF p. 64): "The
sub-gaussian norm of `X` is defined as `‖X‖_{ψ2} = sup_{x∈S^{n-1}} ‖⟨X,x⟩‖_{ψ2}`," reusing the
published scalar sub-gaussian (Orlicz `ψ₂`) norm `HighDimProb.Concentration.subgaussianNorm`
(Definition 2.5.6, per `CAPTAIN_BRIEF.md` Addendum 2 rule 5) applied to each one-dimensional
marginal `⟨X,x⟩`. The supremum ranges over the subtype of unit vectors `{v // ‖v‖ = 1}`, the
book's sphere `Sⁿ⁻¹`. -/
noncomputable def subgaussianVectorNorm {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {n : ℕ}
    (X : Ω → EuclideanSpace ℝ (Fin n)) : ℝ :=
  ⨆ x : {v : EuclideanSpace ℝ (Fin n) // ‖v‖ = 1},
    HighDimProb.Concentration.subgaussianNorm P (fun ω => inner (𝕜 := ℝ) (X ω) x.1)

end HighDimProb.Deviations
