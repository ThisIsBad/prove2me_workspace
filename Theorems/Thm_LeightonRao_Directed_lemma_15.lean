import Mathlib
import Definitions.Def_LeightonRao_Directed_Setting

namespace LeightonRao.Directed

/-- Leighton–Rao, Lemma 15, p. 806. If `T ⊆ V` has `|T| ≥ 2n/3` and either
`∑_{u ∈ V − T} d(T, u) ≥ 1/(4n)` or `∑_{u ∈ V − T} d(u, T) ≥ 1/(4n)`, then some directed cut has
ratio cost at most `12 W` (the constant of Lemma 5's computation, p. 800, with `1/(4n)` in place of
`1/(2n)`). -/
theorem lemma_15 {V : Type} [Fintype V] [DecidableEq V] (N : DiNetwork V)
    (hn : 2 ≤ Fintype.card V) (hconn : IsStronglyConnectedNet N)
    (d : V → V → ℝ) (hd : ∀ u v, 0 ≤ d u v) (T : Finset V)
    (hT : 2 * (Fintype.card V : ℝ) ≤ 3 * (T.card : ℝ))
    (hsum : 1 / (4 * (Fintype.card V : ℝ)) ≤ ∑ u ∈ Tᶜ, diDistFrom N d T u ∨
      1 / (4 * (Fintype.card V : ℝ)) ≤ ∑ u ∈ Tᶜ, diDistTo N d u T) :
    ∃ U : Finset V, U.Nonempty ∧ Uᶜ.Nonempty ∧ diRatio N U ≤ 12 * diTotalWeight N d := by sorry

end LeightonRao.Directed

