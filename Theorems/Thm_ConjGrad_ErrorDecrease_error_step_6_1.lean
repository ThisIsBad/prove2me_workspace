import Mathlib
import Definitions.Def_ConjGrad_ErrorDecrease_cgIter
import Definitions.Def_ConjGrad_ErrorDecrease_errorFun
import Definitions.Def_ConjGrad_ErrorDecrease_rayleigh

open Matrix

namespace ConjGrad.ErrorDecrease

theorem error_step_6_1 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k x₀ h : Fin n → ℝ) (hh : A *ᵥ h = k) (i : ℕ) :
    errorFun A h (cgIter A k x₀ i).x - errorFun A h (cgIter A k x₀ (i + 1)).x =
        cgAlpha A (cgIter A k x₀ i) * ((cgIter A k x₀ i).r ⬝ᵥ (cgIter A k x₀ i).r) ∧
      cgAlpha A (cgIter A k x₀ i) * ((cgIter A k x₀ i).r ⬝ᵥ (cgIter A k x₀ i).r) =
        rayleigh A (cgIter A k x₀ i).p *
          (((cgIter A k x₀ i).x - (cgIter A k x₀ (i + 1)).x) ⬝ᵥ
            ((cgIter A k x₀ i).x - (cgIter A k x₀ (i + 1)).x)) := by sorry

end ConjGrad.ErrorDecrease
