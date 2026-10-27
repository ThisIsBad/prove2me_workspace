import Mathlib
import Definitions.Def_RetroCorr_Separation_Channel
import Definitions.Def_RetroCorr_Separation_TwoWay

namespace RetroCorr.Separation
theorem fig2_noiseless_qubit :
    ∃ P : TwoWayCode (flagLaw 2 2) (retroBranch 2 2) 1 1,
      ∀ ρ : Matrix (QAlgorithms.Qubits 1) (QAlgorithms.Qubits 1) ℂ,
        QAlgorithms.IsDensityMatrix ρ → P.output ρ = ρ := by sorry
end RetroCorr.Separation

