import Mathlib
import Definitions.Def_DermanSeqDecisions_LinProg_Model

open Matrix

open scoped ENNReal

namespace DermanSeqDecisions.LinProg

/-- §3, p. 21 (Derman, *On Sequential Decisions and Markov Chains*, Management Science 9(1):16–24 (1962), DOI 10.1287/mnsc.9.1.16, §3, proof of Theorem 2, the sentence after (7), unnumbered).

Problem 2 under Assumption B (stochastic chance laws, `L` absorbing under every decision,
`w_{Lk} = 0`, `w_{ik} > 0` for `i ≠ L`, `L` reachable from every state under every procedure of
`C′`). Then every `S_R(i)`, `R ∈ C′`, is finite, and a procedure `D* ∈ C′` that minimizes
`(1/(L+1)) ∑_i S_R(i)` over `C′` (the left side of (7), equal to its right side) minimizes `S_R(i)`
over `C′` for every `i = 0, ⋯, L`.

**Formalization Note.** Minimizing `(1/(L+1)) ∑_i S_R(i)` and minimizing `∑_i S_R(i)` are the same;
the latter is stated. Assumption B is encoded as reachability, as in `total_cost_eq_cycle`. -/
theorem avg_minimizer_minimizes_each {S Act : Type*} [Fintype S] [DecidableEq S] [Fintype Act]
    (q : S → Act → S → ℝ) (w : S → Act → ℝ) (L : S) (hq : IsTransitionLaw q)
    (hL : ∀ a, q L a L = 1) (hwL : ∀ a, w L a = 0) (hw : ∀ i a, i ≠ L → 0 < w i a)
    (hB : ∀ D : S → Act → ℝ, IsStationaryRandomized D → ∀ i, ∃ t : ℕ, 0 < (chainMatrix q D ^ t) i L) :
    (∀ D : S → Act → ℝ, IsStationaryRandomized D → ∀ i, totalCost q w D i < ⊤) ∧
    ∀ Dstar : S → Act → ℝ, IsStationaryRandomized Dstar →
      (∀ D : S → Act → ℝ, IsStationaryRandomized D →
        ∑ i, totalCost q w Dstar i ≤ ∑ i, totalCost q w D i) →
      ∀ D : S → Act → ℝ, IsStationaryRandomized D → ∀ i, totalCost q w Dstar i ≤ totalCost q w D i := by sorry

end DermanSeqDecisions.LinProg

