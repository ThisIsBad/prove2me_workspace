import Mathlib
import Definitions.Def_BellmanDP_Markovian_Discrete

namespace BellmanDP.Markovian

/-- Bellman, *Dynamic Programming*, Ch. XI, Theorem 2, p. 329. Under the conditions (10.3a)–(c),
the homogeneous system `λ y_i = Max_q Σ_j a_ij(q) y_j` (10.2) has a positive solution `y` for
exactly one positive constant `λ`; the positive solution is unique up to a positive multiplicative
constant; and `λ = Max_{q ∈ S} φ(q)`, `φ(q)` the Perron root of `A(q)`. -/
theorem perron_eigen_exists_unique {N : ℕ} (hN : 0 < N) {Q : Fin N → Type*}
    (a : (i : Fin N) → Q i → Fin N → ℝ) (S : (i : Fin N) → Set (Q i)) (m : ℝ)
    (h : MarkovHyp a S m) :
    ∃ (lam : ℝ) (y : Fin N → ℝ), 0 < lam ∧ (∀ i, 0 < y i) ∧ IsMaxEigenpair a S lam y ∧
      (∀ (μ : ℝ) (z : Fin N → ℝ), 0 < μ → (∀ i, 0 < z i) → IsMaxEigenpair a S μ z →
        μ = lam ∧ ∃ κ : ℝ, 0 < κ ∧ z = κ • y) ∧
      IsGreatest ((fun q => perronRoot (matOf a q)) '' Set.pi Set.univ S) lam := by sorry

end BellmanDP.Markovian

