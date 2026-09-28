import Mathlib

namespace NonmonotoneLS.Shared

/-- The weights `Q_k` of the nonmonotone line search, Eq. (1.6):
`Q_0 = 1` and `Q_{k+1} = η_k Q_k + 1`. -/
def costQ (η : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => η k * costQ η k + 1

/-- The reference values `C_k` of the nonmonotone line search, Eq. (1.6), along the iterates `x`:
`C_0 = f(x_0)` and `C_{k+1} = (η_k Q_k C_k + f(x_{k+1})) / Q_{k+1}`. -/
noncomputable def costC {E : Type*} (f : E → ℝ) (x : ℕ → E) (η : ℕ → ℝ) : ℕ → ℝ
  | 0 => f (x 0)
  | k + 1 => (η k * costQ η k * costC f x η k + f (x (k + 1))) / costQ η (k + 1)

/-- The average function value `A_k = (1/(k+1)) ∑_{i=0}^{k} f(x_i)` (p. 1044). -/
noncomputable def avgA {E : Type*} (f : E → ℝ) (x : ℕ → E) (k : ℕ) : ℝ :=
  (∑ i ∈ Finset.range (k + 1), f (x i)) / ((k : ℝ) + 1)

end NonmonotoneLS.Shared
