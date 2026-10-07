import Mathlib

namespace BellmanDP.Allocation

/-- Ch. I, § 18, Eq. (18.1), p. 29: `f` solves `f(x) = Max_{0 ≤ y ≤ x} [u(x, y) + f(ay + b(x − y))]`
for every `x ≥ 0`, the maximum being attained. -/
def IsGeneralSolution (u : ℝ → ℝ → ℝ) (a b : ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, 0 ≤ x → IsGreatest ((fun y => u x y + f (a * y + b * (x - y))) '' Set.Icc 0 x) (f x)

/-- Ch. I, Theorem 9, p. 29: the maximum of `φ(x, y)` over the triangle
`0 ≤ y ≤ x ≤ z`, i.e. `Max_{0 ≤ x ≤ z} Max_{0 ≤ y ≤ x} φ(x, y)`. For `φ` continuous and `z ≥ 0` the
triangle is compact and nonempty, so the supremum is attained. -/
noncomputable def triangleMax (φ : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  sSup ((fun p : ℝ × ℝ => φ p.1 p.2) '' {p : ℝ × ℝ | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ z})

end BellmanDP.Allocation
