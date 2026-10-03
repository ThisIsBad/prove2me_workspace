import Mathlib

namespace AppliedComb.Recurrence

/-- Keller–Trotter, Sections 9.3 and 9.5 (pp. 188, 199). The advancement operator `A` on the
real vector space `V` of all functions `f : ℤ → ℝ`, defined by `A f (n) = f (n + 1)`. It is a
linear operator on `V`, so `A ^ p` (composition) satisfies `A ^ p f (n) = f (n + p)`. -/
def advance : Module.End ℝ (ℤ → ℝ) where
  toFun f := fun n => f (n + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Keller–Trotter, Section 9.5 (p. 199, Eq. (9.5.1)). The advancement operator polynomial
`p(A) = c₀ A^k + c₁ A^(k-1) + c₂ A^(k-2) + ⋯ + c_k` with real coefficients `c₀, …, c_k`,
as a linear operator on `V = (ℤ → ℝ)`. The coefficient `c i` multiplies `A ^ (k - i)`
(here `i ≤ k`, so the natural-number subtraction is exact). -/
noncomputable def opPoly (k : ℕ) (c : Fin (k + 1) → ℝ) : Module.End ℝ (ℤ → ℝ) :=
  ∑ i : Fin (k + 1), c i • advance ^ (k - (i : ℕ))

/-- Keller–Trotter, Section 9.5 (p. 199). The set `W` of all solutions `f : ℤ → ℝ` of the
homogeneous equation `(c₀ A^k + c₁ A^(k-1) + ⋯ + c_k) f = 0`, i.e. the kernel of `p(A)`,
as a subspace of `V`. -/
noncomputable def solutionSpace (k : ℕ) (c : Fin (k + 1) → ℝ) : Submodule ℝ (ℤ → ℝ) :=
  LinearMap.ker (opPoly k c)

end AppliedComb.Recurrence
