import Mathlib

namespace ThreeOpSplitting.Accel

/-- The state `(x_A^k, x_B^k, u_B^k)` of Algorithm 3 after `k` iterations. -/
structure AccelState (H : Type*) where
  /-- `x_A^k` -/
  xA : H
  /-- `x_B^k` -/
  xB : H
  /-- `u_B^k` -/
  uB : H

/-- Algorithm 3 of Davis–Yin (Algorithm 1 with acceleration), equivalently recursion (3.8),
with resolvent families `JA γ = J_{γA}`, `JB γ = J_{γB}`, single-valued `C`, stepsizes
`γ : ℕ → ℝ` and initial point `x_A^0 = xA0`:

* `x_B^0 = J_{γ₀B}(x_A^0)`, `u_B^0 = (1/γ₀)(x_A^0 - x_B^0)`;
* for `k ≥ 0`:
  `x_B^{k+1} = J_{γ_k B}(x_A^k + γ_k u_B^k)`,
  `u_B^{k+1} = (1/γ_k)(x_A^k + γ_k u_B^k - x_B^{k+1})`,
  `x_A^{k+1} = J_{γ_{k+1} A}(x_B^{k+1} - γ_{k+1} u_B^{k+1} - γ_{k+1} C x_B^{k+1})`. -/
noncomputable def accelIter {H : Type*} [AddCommGroup H] [Module ℝ H]
    (JA JB : ℝ → H → H) (C : H → H) (γ : ℕ → ℝ) (xA0 : H) : ℕ → AccelState H
  | 0 =>
    { xA := xA0
      xB := JB (γ 0) xA0
      uB := (γ 0)⁻¹ • (xA0 - JB (γ 0) xA0) }
  | k + 1 =>
    let s := accelIter JA JB C γ xA0 k
    let xB' := JB (γ k) (s.xA + γ k • s.uB)
    let uB' := (γ k)⁻¹ • (s.xA + γ k • s.uB - xB')
    { xA := JA (γ (k + 1)) (xB' - γ (k + 1) • uB' - γ (k + 1) • C xB')
      xB := xB'
      uB := uB' }

end ThreeOpSplitting.Accel
