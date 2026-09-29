import Mathlib
import Definitions.Def_ConjGrad_ErrorDecrease_cgIter
import Definitions.Def_ConjGrad_ErrorDecrease_errorFun

open Matrix

namespace ConjGrad.ErrorDecrease

theorem error_diff_6_2 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k x₀ h : Fin n → ℝ) (hh : A *ᵥ h = k) (i j : ℕ) (hij : i < j) :
    errorFun A h (cgIter A k x₀ i).x - errorFun A h (cgIter A k x₀ j).x =
      ∑ l ∈ Finset.Ico i j,
        cgAlpha A (cgIter A k x₀ l) * ((cgIter A k x₀ l).r ⬝ᵥ (cgIter A k x₀ l).r) := by sorry

end ConjGrad.ErrorDecrease
