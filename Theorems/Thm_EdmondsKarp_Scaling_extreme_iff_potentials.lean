import Mathlib
import Definitions.Def_EdmondsKarp_Scaling_Transport

namespace EdmondsKarp.Scaling

/-- Theorem 8 (p. 259). For the Hitchcock network of Figure 1 with positive capacities `a_i`, `b_j`,
`∑ a_i = ∑ b_j` and nonnegative costs `d_ij`, a maximum flow `f` is extreme (of minimum cost among
the maximum flows) if and only if there exist real `u_0, u_1, …, u_m` and `v_0, v_1, …, v_n` with
(5a)–(5f). The page prints `v_0, …, v_m`; the index of `v` runs over `0, …, n` as (5a)–(5f) show.
"Extreme among maximum flows" is read with `f` ranging over maximum flows (hypothesis `hx`): the zero
flow satisfies (5a)–(5f) for suitable potentials but is not maximum. -/
theorem extreme_iff_potentials {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (T : Transport m n)
    (ha : ∀ i, 0 < T.a i) (hb : ∀ j, 0 < T.b j) (hsum : ∑ i, T.a i = ∑ j, T.b j)
    (hd : ∀ i j, 0 ≤ T.d i j) (x : Flow m n) (hx : IsMaxFlow T x) :
    IsExtreme T x ↔
      ∃ (u0 : ℝ) (u : Fin m → ℝ) (v0 : ℝ) (v : Fin n → ℝ),
        (∀ i j, 0 ≤ u i - v j + T.d i j) ∧
        (∀ i j, 0 < u i - v j + T.d i j → x.fx i j = 0) ∧
        (∀ i, u0 > u i → x.f0 i = 0) ∧
        (∀ i, u0 < u i → x.f0 i = T.a i) ∧
        (∀ j, v j > v0 → x.fz j = 0) ∧
        (∀ j, v j < v0 → x.fz j = T.b j) := by sorry

end EdmondsKarp.Scaling
