import Mathlib
import Definitions.Def_BellmanDP_Allocation_Model

namespace BellmanDP.Allocation

/-- Ch. I, § 11, p. 17–19: the quantities left at the successive stages when the stationary
policy `y₀` is used from the initial quantity `x`: `x₀ = x`,
`x_{n+1} = a y₀(x_n) + b (x_n − y₀(x_n))`. -/
def policyTrajectory (a b : ℝ) (y₀ : ℝ → ℝ) (x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 =>
      a * y₀ (policyTrajectory a b y₀ x n) + b * (policyTrajectory a b y₀ x n - y₀ (policyTrajectory a b y₀ x n))

/-- Ch. I, § 11, Eqs. (11.5) and (11.10), pp. 18–19: the total return of the stationary policy
`y₀`, the series `f₀(x) = g(y₀) + h(x − y₀) + …` obtained by iterating
`f₀(x) = T(f₀, y₀(x))`. -/
noncomputable def policyReturn (g h : ℝ → ℝ) (a b : ℝ) (y₀ : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑' n : ℕ, (g (y₀ (policyTrajectory a b y₀ x n)) +
    h (policyTrajectory a b y₀ x n - y₀ (policyTrajectory a b y₀ x n)))

end BellmanDP.Allocation
