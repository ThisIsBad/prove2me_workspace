import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_AccelVI_AVC_Setting

namespace AccelVI.AVC

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]

/-- Lemma 5.2, p. 8: with `x^π = (v^π, v^π)` and `x_s = (v_s, v_{s−1})`, the A-VC iterates with
step sizes (4.1) satisfy `x_s = x^π + B_π^{s−1}(x_1 − x^π)` for every `s ≥ 1`. -/
theorem lemma_5_2 (M : MDP S A) (hM : M.Valid) (pol : S → A → ℝ) (hpol : FoundationsML.ReinforcementLearning.IsPolicy pol)
    (v0 v1 : S → ℝ) (s : ℕ) (hs : 1 ≤ s) :
    xvec (avc M pol (alphaAVC M.lam) (gammaAVC M.lam) v0 v1) s =
      xPi M pol + ((Bpol M pol) ^ (s - 1)).mulVec
        (xvec (avc M pol (alphaAVC M.lam) (gammaAVC M.lam) v0 v1) 1 - xPi M pol) := by sorry

end AccelVI.AVC

