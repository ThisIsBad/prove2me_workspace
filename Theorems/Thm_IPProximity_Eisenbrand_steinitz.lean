import Mathlib

namespace IPProximity.Eisenbrand

/-- Theorem 1.1 (Steinitz) with Sevast'anov's constant `c(m) = m` (p. 5:4): in an
`m`-dimensional real normed space, vectors of norm at most `1` summing to zero can be ordered so
that every partial sum `x_{π(1)} + ⋯ + x_{π(k)}`, `1 ≤ k ≤ n`, has norm at most `m`. -/
theorem steinitz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {m n : ℕ} (hdim : Module.finrank ℝ E = m) (x : Fin n → E)
    (hsum : ∑ i, x i = 0) (hnorm : ∀ i, ‖x i‖ ≤ 1) :
    ∃ σ : Equiv.Perm (Fin n), ∀ k : ℕ, 1 ≤ k → k ≤ n →
      ‖∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < k), x (σ j)‖ ≤ (m : ℝ) := by sorry

end IPProximity.Eisenbrand

