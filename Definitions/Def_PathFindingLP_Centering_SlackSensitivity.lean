import Mathlib
import Definitions.Def_PathFindingLP_Centering_WeightedCentralPath

open Matrix

namespace PathFindingLP.Centering

variable {m n : ℕ}

/-- The projection matrix of Definition 2 (§IV.B, p. 428):
`P_{S⁻¹A}(w) = W^{1/2} S⁻¹ A (Aᵀ S⁻¹ W S⁻¹ A)⁻¹ Aᵀ S⁻¹ W^{1/2}`, with `S = diag(s)`,
`W = diag(w)`, `W^{1/2} = diag(√wᵢ)` and `S⁻¹ = diag(1 / sᵢ)`. -/
noncomputable def projectionMatrix (A : Matrix (Fin m) (Fin n) ℝ) (s w : Fin m → ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  diagonal (fun i => Real.sqrt (w i)) * diagonal (fun i => (s i)⁻¹) * A *
    (weightedGram A s w)⁻¹ * Aᵀ * diagonal (fun i => (s i)⁻¹) *
    diagonal (fun i => Real.sqrt (w i))

/-- The slack sensitivity of Definition 2 (§IV.B, p. 428):
`γ(s, w) = max_{i ∈ [m]} ‖W^{-1/2} 𝟙ᵢ‖_{P_{S⁻¹A}(w)}`, where `𝟙ᵢ` is the `i`-th standard basis
vector and `W^{-1/2} = diag(1 / √wᵢ)`. The maximum over the finite index set is written as a
supremum over `Fin m`. -/
noncomputable def slackSensitivity (A : Matrix (Fin m) (Fin n) ℝ) (s w : Fin m → ℝ) : ℝ :=
  ⨆ i : Fin m,
    matNorm (projectionMatrix A s w)
      (diagonal (fun j => (Real.sqrt (w j))⁻¹) *ᵥ Pi.single i (1 : ℝ))

end PathFindingLP.Centering
