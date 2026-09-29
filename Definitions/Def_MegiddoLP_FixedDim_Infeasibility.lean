import Mathlib

/-!
The infeasibility function of a linear system (Megiddo, J. ACM 31 (1984), §4, p. 123).

For the system `Σⱼ a_ij xⱼ ≥ bᵢ (i = 1, …, n)` the paper defines
`f(x) = max {bᵢ - Σⱼ a_ij xⱼ : i = 1, …, n}`. It is defined here for a system with at
least one constraint (rows indexed by `Fin (n + 1)`), so the maximum is over a nonempty
finite set; `x` satisfies the system iff `f x ≤ 0`.
-/

namespace MegiddoLP.FixedDim

/-- `f(x) = max_i (bᵢ - Aᵢ ⬝ᵥ x)` over the `n + 1` rows of `A`. -/
noncomputable def infeas {n d : ℕ} (A : Matrix (Fin (n + 1)) (Fin d) ℝ) (b : Fin (n + 1) → ℝ)
    (x : Fin d → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => b i - A i ⬝ᵥ x)

end MegiddoLP.FixedDim
