import Definitions.Def_BirkhoffGlobalSection_AmbientRotation

namespace BirkhoffGlobalSection

theorem saddle_center_spectral_splitting :
    ∃ ω lam : ℝ, 0 < ω ∧ 0 < lam ∧ ∃ e₁ e₂ f₁ f₂ : Phase,
      TangentialHessian.qI.mulVec
        (((!![-16, 0, 0, 1; 0, 8, -1, 0; 0, -1, 1, 0; 1, 0, 0, 1] :
          Matrix (Fin 4) (Fin 4) ℝ).mulVec e₁)) = ω • e₂ ∧
      TangentialHessian.qI.mulVec
        (((!![-16, 0, 0, 1; 0, 8, -1, 0; 0, -1, 1, 0; 1, 0, 0, 1] :
          Matrix (Fin 4) (Fin 4) ℝ).mulVec e₂)) = -ω • e₁ ∧
      TangentialHessian.qI.mulVec
        (((!![-16, 0, 0, 1; 0, 8, -1, 0; 0, -1, 1, 0; 1, 0, 0, 1] :
          Matrix (Fin 4) (Fin 4) ℝ).mulVec f₁)) = lam • f₁ ∧
      TangentialHessian.qI.mulVec
        (((!![-16, 0, 0, 1; 0, 8, -1, 0; 0, -1, 1, 0; 1, 0, 0, 1] :
          Matrix (Fin 4) (Fin 4) ℝ).mulVec f₂)) = -lam • f₂ ∧
      LinearIndependent ℝ ![e₁, e₂, f₁, f₂] := by sorry

end BirkhoffGlobalSection
