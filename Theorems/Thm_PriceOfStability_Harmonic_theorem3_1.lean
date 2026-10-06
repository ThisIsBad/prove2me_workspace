import Mathlib
import Definitions.Def_PriceOfStability_Harmonic_Model

open CongestionPoA.AsymSum

namespace PriceOfStability.Harmonic

/-- Anshelevich et al., *The Price of Stability for Network Design with Fair Cost Allocation*, SIAM J.
Comput. 38 (2008), Theorem 3.1, p. 1609 (PDF p. 8), proof p. 1610 (PDF p. 9): if the potential `Φ` of (2.1)
satisfies `cost(S) ≤ A · Φ(S)` and `Φ(S) ≤ B · cost(S)` for all `S`, then the price of
stability is at most `A · B`: some pure Nash equilibrium `S` has `cost(S) ≤ A · B · cost(P)`
for every strategy vector `P`.

**Formalization Note.** Stated for every congestion game with arbitrary edge functions `f_e`;
`cost(S) = Σᵢ Cᵢ(S)` is `sumCost` (for a fair game it equals the cost of the designed
network, by `shapley_budget_balance`). "All S" ranges over feasible strategy vectors. The
hypothesis `0 ≤ A` is implicit in the paper: its proof uses `A · Φ(S′) ≤ A · Φ(S*)`.
The price of stability is stated in existence form, without dividing by the optimum; the
existence of a profile (every `Σᵢ` nonempty) is assumed. -/
theorem theorem3_1 {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (G : CongestionGame ι E) (A B : ℝ) (hA : 0 ≤ A)
    (hcost : ∀ S, IsProfile G S → sumCost G S ≤ A * potential G S)
    (hpot : ∀ S, IsProfile G S → potential G S ≤ B * sumCost G S)
    (hP : ∃ P, IsProfile G P) :
    ∃ S, IsPureNash G S ∧ ∀ P, IsProfile G P → sumCost G S ≤ A * B * sumCost G P := by sorry

end PriceOfStability.Harmonic

