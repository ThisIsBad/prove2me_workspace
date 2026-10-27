import Mathlib
import Definitions.Def_RetroCorr_Separation_Channel

namespace RetroCorr.Separation
theorem echo_effect (c : ℕ) (W : Matrix.unitaryGroup (Fin c) ℂ) (i j : Fin c) :
    QAlgorithms.effectProb (Matrix.kronecker (transposeBasisProj W i) (basisProj W j))
      (maxEntDensity c) = if i = j then ((c : ℝ))⁻¹ else 0 := by sorry
end RetroCorr.Separation

