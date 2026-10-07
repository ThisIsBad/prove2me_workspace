import Mathlib
import Definitions.Def_BellmanDP_Markovian_ScalarGame

namespace BellmanDP.Markovian

open Filter Topology

/-- Bellman, *Dynamic Programming*, Ch. XI, Theorem 5, p. 333. Let `A`, `B` be `m × n` matrices
(`m, n ≥ 1`) with `(Bp, q) ≥ d > 0` for all probability vectors `p`, `q`, and let `u` solve the
scalar equation `du/dt = Max_p Min_q [(Ap, q) − (Bp, q) u]`, `u(0) = c`, for `t ≥ 0` (in integral
form). Then `lim_{t → ∞} u(t) = Max_p Min_q (Ap, q)/(Bp, q) = Min_q Max_p (Ap, q)/(Bp, q)`. -/
theorem scalar_game_limit {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (A B : Matrix (Fin m) (Fin n) ℝ) (d : ℝ) (hd : 0 < d)
    (hB : ∀ p ∈ stdSimplex ℝ (Fin n), ∀ q ∈ stdSimplex ℝ (Fin m), d ≤ pairing B p q)
    (c : ℝ) (u : ℝ → ℝ) (hu_cont : ContinuousOn u (Set.Ici 0))
    (hu : ∀ t : ℝ, 0 ≤ t → u t = c + ∫ s in (0 : ℝ)..t, gameRHS A B (u s)) :
    Tendsto u atTop (𝓝 (maxMinRatio A B)) ∧ maxMinRatio A B = minMaxRatio A B := by sorry

end BellmanDP.Markovian

