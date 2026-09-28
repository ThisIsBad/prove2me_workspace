import Mathlib
import Definitions.Def_GallegoOzerADI_PositiveSetup_ABConvex

namespace GallegoOzerADI.PositiveSetup

theorem abConvex_add (a b a' b' : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (ha' : 0 ≤ a') (hb' : 0 ≤ b')
    (f g : ℝ → ℝ) (hf : ABConvex a b f) (hg : ABConvex a' b' g) (α β : ℝ) (hα : 0 < α)
    (hβ : 0 < β) :
    ABConvex (α * a + β * a') (α * b + β * b') (fun x => α * f x + β * g x) := by sorry

end GallegoOzerADI.PositiveSetup
