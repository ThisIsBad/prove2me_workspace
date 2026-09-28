import Mathlib
import Definitions.Def_GallegoOzerADI_PositiveSetup_ABConvex

namespace GallegoOzerADI.PositiveSetup

end GallegoOzerADI.PositiveSetup

open GallegoOzerADI.PositiveSetup

theorem solution (a b a' b' : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (ha' : 0 ≤ a') (hb' : 0 ≤ b')
    (f g : ℝ → ℝ) (hf : ABConvex a b f) (hg : ABConvex a' b' g) (α β : ℝ) (hα : 0 < α)
    (hβ : 0 < β) :
    ABConvex (α * a + β * a') (α * b + β * b') (fun x => α * f x + β * g x) := by
  intro x₁ x₂ hx θ hθ0 hθ1
  have h1 := hf x₁ x₂ hx θ hθ0 hθ1
  have h2 := hg x₁ x₂ hx θ hθ0 hθ1
  have e1 := mul_le_mul_of_nonneg_left h1 hα.le
  have e2 := mul_le_mul_of_nonneg_left h2 hβ.le
  simp only
  nlinarith [e1, e2]
