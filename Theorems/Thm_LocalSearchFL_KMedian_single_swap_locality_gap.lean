import Mathlib
import Definitions.Def_LocalSearchFL_KMedian_kmCost

namespace LocalSearchFL.KMedian

/-- Theorem 3.2 (p. 551): single-swap local search for the metric k-median problem has locality
gap at most 5. If `S` is a set of `k` facilities that is locally optimum for single swaps, then
`cost(S) ≤ 5 · cost(O)` for every nonempty set `O` of at most `k` facilities. -/
theorem single_swap_locality_gap {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl]
    [Fintype Fa] [DecidableEq Fa]
    (I : LocalSearchFL.Shared.MetricInstance Cl Fa) (k : ℕ) (S : Finset Fa) (hS : S.Nonempty) (hSk : S.card = k)
    (hloc : IsSwapLocalOpt I S hS)
    (O : Finset Fa) (hO : O.Nonempty) (hOk : O.card ≤ k) :
    kmCost I S hS ≤ 5 * kmCost I O hO := by sorry

end LocalSearchFL.KMedian

