import Mathlib
import Definitions.Def_LocalSearchFL_MultiSwap_kmCost

namespace LocalSearchFL.MultiSwap

/-- §3.4, p. 553 (announced §3.3, p. 551): p-swap local search for the metric k-median problem
has locality gap at most `3 + 2/p`. If `p ≥ 1` and `S` is a set of `k` facilities that is locally
optimum for the neighbourhood (3), then `cost(S) ≤ (3 + 2/p) · cost(O)` for every nonempty set
`O` of at most `k` facilities. -/
theorem multiswap_locality_gap {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl]
    [Fintype Fa] [DecidableEq Fa]
    (I : LocalSearchFL.Shared.MetricInstance Cl Fa) (p : ℕ) (hp : 1 ≤ p)
    (k : ℕ) (S : Finset Fa) (hS : S.Nonempty) (hSk : S.card = k)
    (hloc : IsPSwapLocalOpt I p S hS)
    (O : Finset Fa) (hO : O.Nonempty) (hOk : O.card ≤ k) :
    kmCost I S hS ≤ (3 + 2 / (p : ℝ)) * kmCost I O hO := by sorry

end LocalSearchFL.MultiSwap

