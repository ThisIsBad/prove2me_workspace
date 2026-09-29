import Mathlib
import Definitions.Def_HooftMonopole_Defs

open MeasureTheory Filter Topology Real

namespace HooftMonopole

theorem radial_W_equation (e lam F : ℝ) (q w : ℝ → ℝ)
    (hsol : IsStaticSolution e lam F (hedgehogHiggs q) (hedgehogGauge w)) :
    ∀ r : ℝ, 0 < r → radialWEquation e w q r := by sorry

end HooftMonopole
