import Mathlib
import Definitions.Def_HassinRSP_Rounding_Setting

namespace HassinRSP.Rounding

theorem rounding_error (I : Instance) (hI : I.WellFormed) (ε : ℝ) (hε0 : 0 < ε)
    (V : ℝ) (hV : 0 < V) :
    (∀ e ∈ I.E, V * ε / ((I.n : ℝ) - 1) * roundLen I ε V e ≤ I.c e ∧
      (I.c e : ℝ) - V * ε / ((I.n : ℝ) - 1) * roundLen I ε V e ≤ V * ε / ((I.n : ℝ) - 1)) ∧
    (∀ (i j : ℕ) (p : List ℕ), IsPathIn I.E i j p →
      V * ε / ((I.n : ℝ) - 1) * roundPathLen I ε V p ≤ pathLen I p ∧
      (pathLen I p : ℝ) - V * ε / ((I.n : ℝ) - 1) * roundPathLen I ε V p ≤ V * ε) := by sorry

end HassinRSP.Rounding

