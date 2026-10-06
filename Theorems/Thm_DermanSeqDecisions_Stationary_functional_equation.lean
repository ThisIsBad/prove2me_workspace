import Mathlib
import Definitions.Def_SennottDP_AvgFinite_Model
import Definitions.Def_SennottDP_AvgFinite_Criteria

open scoped ENNReal NNReal
open SennottDP.AvgFinite

namespace DermanSeqDecisions.Stationary

/-- The functional equation of the discounted problem (Derman, *On Sequential Decisions and Markov
Chains*, Management Science 9(1):16–24 (1962), DOI 10.1287/mnsc.9.1.16, §2, proof of Theorem 1,
p. 19, unnumbered display). States `S` (Derman's `0, …, L`) and decisions `Act` (Derman's
`d_1, …, d_K`) are finite, every decision is available in every state, `M.P i k j = q_ij(k)` and
`M.C i k = w_ik ≥ 0`. For `0 < α < 1` let `V_i = min_{R ∈ C} V_R(i, α)` be the optimal discounted
cost over all history-dependent randomized procedures. Then `V_i` is the minimum, over all
randomizations `D_i = (D_i1, …, D_iK)` (`D_ik ≥ 0`, `∑_k D_ik = 1`), of
`∑_k D_ik (w_ik + α ∑_j q_ij(k) V_j)`; in particular the minimum is attained.

**Formalization Note.** `V_i` is `discValue M α i`, the infimum of `discCost θ α i` over all
`θ : Policy M` (Derman's class `C`), valued in `[0, ∞]`. The randomization `D_i` is a function
`Act → [0, ∞]` summing to `1` (so each `D_ik ∈ [0, 1]`). "min" is `IsLeast`: the value belongs to
the set of attained right-hand sides and is below each of them. The costs are only assumed
nonnegative: the proof of Theorem 1 uses this equation for Problem 1 (`w_ik > 0`) and for
Problem 2 (`w_Lk = 0`) alike. -/
theorem functional_equation {S : Type*} {Act : Type*} [Fintype S] [Nonempty S]
    [Fintype Act] [Nonempty Act]
    (M : MDC S Act) (hA : ∀ i, M.A i = Finset.univ) (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    (i : S) :
    IsLeast
      {x : ℝ≥0∞ | ∃ D : Act → ℝ≥0∞, ∑ k, D k = 1 ∧
        x = ∑ k, D k * ((M.C i k : ℝ≥0∞) + ENNReal.ofReal α * ∑ j, M.P i k j * discValue M α j)}
      (discValue M α i) := by sorry

end DermanSeqDecisions.Stationary

