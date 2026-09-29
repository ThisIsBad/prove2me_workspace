import Mathlib

namespace DiophantinePreprocessing.FrankTardos

/-- The ℓ∞ norm `‖v‖∞ = max_j |v(j)|` of an integer vector, as a natural number
(it is `0` for the zero vector and for `n = 0`). -/
def supNorm {n : ℕ} (v : Fin n → ℤ) : ℕ :=
  Finset.univ.sup (fun j => (v j).natAbs)

/-- Condition (iii) of Frank–Tardos, Theorem 3.1, for a decomposition `w = ∑_{i=1}^k λ_i v_i`
indexed by `i = 1, …, k`: for `i = 2, …, k` the vector `v_i` is nonzero and
`λ_i / λ_{i-1} ≤ 1 / (N ‖v_i‖∞)`, written multiplicatively as `λ_i · N · ‖v_i‖∞ ≤ λ_{i-1}`. -/
def CondIII {n : ℕ} (N k : ℕ) (lam : ℕ → ℝ) (v : ℕ → Fin n → ℤ) : Prop :=
  ∀ i ∈ Finset.Icc 2 k, v i ≠ 0 ∧ lam i * ((N : ℝ) * (supNorm (v i) : ℝ)) ≤ lam (i - 1)

end DiophantinePreprocessing.FrankTardos
