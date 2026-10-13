import Mathlib
import Definitions.Def_StrategyProofArrow_WeakArrow_Basic

namespace StrategyProofArrow.WeakArrow

/-- **Theorem 3' (Arrow)**, Satterthwaite p. 49: for a committee with `n ≥ 2` and `m ≥ 3`, whose
ballots are weak orders, a social welfare function satisfying CS, NNR and IIA is dictatorial: some
individual `i` exists such that, at every ballot set `B`, `x B̄_i y` implies `x Ā y`. -/
theorem theorem_3_prime {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι] [DecidableEq A]
    (hn : 2 ≤ Fintype.card ι) (hm : 3 ≤ Fintype.card A)
    (u : WeakProfile ι A → WeakOrder A)
    (hCS : CS u) (hNNR : NNR u) (hIIA : IIA u) :
    Dictatorial u := by sorry

end StrategyProofArrow.WeakArrow

