import Mathlib
import Definitions.Def_MassiveChannels_GCE_Model

set_option autoImplicit false

noncomputable section

namespace MassiveChannels.GCE

open QAlgorithms
open QAlgorithms.Papers.Independent.Dependency50.P07
open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

/-- Orthogonal pure states transmit their full classical label entropy. -/
theorem accessible_eq_holevo_of_orthogonal_pure {Q : Type} [Fintype Q]
    [DecidableEq Q] [Nonempty Q]
    (v : OrthonormalBasis Q ℂ (EuclideanSpace ℂ Q)) (p : Q → ℝ)
    (hp : (∀ j, 0 ≤ p j) ∧ (∑ j, p j) = 1) :
    let e : CQData Q Q := ⟨p, fun j => pureDensity (v j)⟩
    e.Valid ∧ accessibleInformation e = ensembleInformation e ∧
      ensembleInformation e = shannon p ∧
      shannon p = vnEntropy (ensembleMean e) := by sorry

end MassiveChannels.GCE

