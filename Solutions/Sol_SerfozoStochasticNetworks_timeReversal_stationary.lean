import Mathlib
import Definitions.Def_SerfozoStochasticNetworks_Reversible

open SerfozoStochasticNetworks

theorem solution {E : Type*} (q qbar : E → E → ℝ) (π : E → ℝ)
    (hπ : ∀ x, 0 < π x) (hq : ∀ x, Summable (q x)) (hqbar : ∀ x, Summable (qbar x))
    (hin : ∀ x, Summable fun y => π y * q y x)
    (hrev : ∀ x y, qbar x y = (π x)⁻¹ * π y * q y x)
    (hrate : ∀ x, ∑' y, q x y = ∑' y, qbar x y) :
    IsInvariant q π := by
  intro x
  rw [hrate x]
  have e : (fun y => qbar x y) = fun y => (π x)⁻¹ * (π y * q y x) := by
    funext y; rw [hrev x y, mul_assoc]
  rw [show (∑' y, qbar x y) = ∑' y, (π x)⁻¹ * (π y * q y x) from congrArg tsum e,
    tsum_mul_left, ← mul_assoc, mul_inv_cancel₀ (hπ x).ne', one_mul]
