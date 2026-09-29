import Mathlib

namespace PolyhedralSOC.UpperBound

/-- The system of linear inequalities (8) of Ben-Tal & Nemirovski, *On Polyhedral
Approximations of the Second-Order Cone*, Math. Oper. Res. 26(2):193–205 (2001), §2,
p. 199 (PDF p. 7), with parameter `ν`, in the variables `x₁, x₂, x₃` and `ξ^j, η^j`
(`j = 0, …, ν`; `ξ j`, `η j` for `j > ν` are never constrained):
(a) `ξ^0 ≥ |x₁|`, `η^0 ≥ |x₂|`;
(b) `ξ^j = cos(π/2^{j+1}) ξ^{j−1} + sin(π/2^{j+1}) η^{j−1}`,
    `η^j ≥ |−sin(π/2^{j+1}) ξ^{j−1} + cos(π/2^{j+1}) η^{j−1}|`, `j = 1, …, ν`;
(c) `ξ^ν ≤ x₃`, `η^ν ≤ tan(π/2^{ν+1}) ξ^ν`. -/
def System8 (ν : ℕ) (x₁ x₂ x₃ : ℝ) (ξ η : ℕ → ℝ) : Prop :=
  (ξ 0 ≥ |x₁| ∧ η 0 ≥ |x₂|) ∧
  (∀ j : ℕ, 1 ≤ j → j ≤ ν →
    ξ j = Real.cos (Real.pi / 2 ^ (j + 1)) * ξ (j - 1)
            + Real.sin (Real.pi / 2 ^ (j + 1)) * η (j - 1) ∧
    η j ≥ |-Real.sin (Real.pi / 2 ^ (j + 1)) * ξ (j - 1)
            + Real.cos (Real.pi / 2 ^ (j + 1)) * η (j - 1)|) ∧
  (ξ ν ≤ x₃ ∧ η ν ≤ Real.tan (Real.pi / 2 ^ (ν + 1)) * ξ ν)

/-- The accuracy `δ(ν) = 1 / cos(π/2^{ν+1}) − 1` of the system (8)
(Ben-Tal & Nemirovski 2001, Proposition 2.1, Eq. (9), p. 199 (PDF p. 7)). -/
noncomputable def delta (ν : ℕ) : ℝ :=
  1 / Real.cos (Real.pi / 2 ^ (ν + 1)) - 1

end PolyhedralSOC.UpperBound
