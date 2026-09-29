import Mathlib
import Definitions.Def_KServer_model

namespace CompetitivePaging.Combining

/-- Fiat et al. 1991, §6, proof of Theorem 6 (necessity), pp. 9–10. Vertex set `M` of size
`2m`, enumerated by `e : Fin m × Fin 2 ≃ M` (`e (i, 0)` and `e (i, 1)` are the paper's
vertices `i` and `i + m`), with the uniform metric; `2m − 1` servers. There are deterministic
on-line algorithms `B(1), …, B(m)` such that `B(i)` keeps every vertex other than `e (i, 0)`,
`e (i, 1)` covered at all times; at every step of every request sequence the movement costs of
all of them add up to at most `1` (no two of them ever move a server at the same step, and each
moves at most one server); hence on every request sequence `σ` their total cost is at most the
length of `σ`. -/
theorem exists_shuttle_algorithms {m : ℕ} (hm : 0 < m) {M : Type} [MetricSpace M]
    (hM : ∀ x y : M, x ≠ y → dist x y = 1) (e : Fin m × Fin 2 ≃ M) :
    ∃ B : Fin m → KServer.OnlineAlgorithm (2 * m - 1) M,
      (∀ (i : Fin m) (l : List M) (x : M), x ≠ e (i, 0) → x ≠ e (i, 1) →
          ∃ j, (B i).conf l j = x) ∧
      (∀ (σ : List M) (s : ℕ), s < σ.length →
          ∑ i, KServer.moveCost ((B i).conf (σ.take s)) ((B i).conf (σ.take (s + 1))) ≤ 1) ∧
      ∀ σ : List M, ∑ i, (B i).cost σ ≤ (σ.length : ℝ) := by sorry

end CompetitivePaging.Combining

