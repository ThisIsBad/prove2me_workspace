import Mathlib
import Definitions.Def_KServer_model

namespace CompetitivePaging.Combining

/-- Fiat et al. 1991, §6, proof of Theorem 6 (necessity), p. 10. With `2m − 1` servers on a
vertex set `M` of size `2m` (enumerated by `e : Fin m × Fin 2 ≃ M`) with the uniform metric,
for every deterministic on-line algorithm `A` and every `N` there is a request sequence `τ(N)` of
length `N` that causes `A` to move a server at every step; hence `C_A(τ(N)) ≥ N`. -/
theorem exists_sequence_forcing_moves {m : ℕ} (hm : 0 < m) {M : Type} [MetricSpace M]
    (hM : ∀ x y : M, x ≠ y → dist x y = 1) (e : Fin m × Fin 2 ≃ M)
    (A : KServer.OnlineAlgorithm (2 * m - 1) M) (N : ℕ) :
    ∃ τ : List M, τ.length = N ∧
      (∀ j < N, A.conf (τ.take j) ≠ A.conf (τ.take (j + 1))) ∧
      (N : ℝ) ≤ A.cost τ := by sorry

end CompetitivePaging.Combining

