import Mathlib
import Definitions.Def_TsengCGD_Linear_Basic
import Definitions.Def_TsengCGD_ErrorBound_Conditions

namespace TsengCGD.ErrorBound

theorem lemma6 :
    ∀ K : ℝ, 0 ≤ K → ∃ κ > 0, ∀ {n : ℕ} (f : TsengCGD.Global.Vec n → ℝ) (D : Set (TsengCGD.Global.Vec n)) (P : TsengCGD.Global.Vec n → ℝ) (c : ℝ),
      TsengCGD.Global.Standing f D P c → PLipOn D P K →
        ∀ x ∈ D, ∀ (dt : TsengCGD.Global.Vec n) (δt : ℝ), IsEpiSubSol f D P c x (P x) dt δt →
          pairNorm dt δt ≤ κ * ‖TsengCGD.Global.dI f D P c x‖ := by sorry

end TsengCGD.ErrorBound

