import Mathlib
import Definitions.Def_JewellMRP_InfiniteStep_Model
import Definitions.Def_DermanSeqDecisions_LinProg_Model

open Matrix

open scoped ENNReal

namespace DermanSeqDecisions.LinProg

/-- (7), p. 21 (Derman, *On Sequential Decisions and Markov Chains*, Management Science 9(1):16–24 (1962), DOI 10.1287/mnsc.9.1.16, §3, proof of Theorem 2, display (7)).

Problem 2 under Assumption B: the chance laws are stochastic, `L` is absorbing under every decision,
`w_{Lk} = 0`, `w_{ik} > 0` for `i ≠ L`, and for every procedure of `C′` the state `L` is
reachable from every state. Adjoin the state `−1` (`none`) as on p. 21. For every `D ∈ C′`
(extended to `−1` by any decision probabilities `D₀`) and every stationary vector `π` of the
augmented chain `P`, with `f(j) = ∑_k D_{jk} w_{jk}` (`f(−1) = 0`):
`π_{−1} > 0`, the taboo probabilities `_{−1}p^{(t)}_{−1,j}` are summable in `t`, and
$$\frac{1}{L+1}\sum_{i=0}^{L} S_R(i) = \sum_{t=0}^{\infty}\sum_{j=-1}^{L} {}_{-1}p^{(t)}_{-1,j} f(j)
  = \frac{1}{\pi_{-1}}\sum_{j=-1}^{L}\pi_j f(j).$$

**Formalization Note.** `L + 1` is `Fintype.card S`. Assumption B ("`L` is accessible from
`0, ⋯, L − 1` within a finite number of transitions with probability 1") is stated as
reachability, `∀ i, ∃ t, 0 < (P_D^t)_{iL}`: for a finite chain in which `L` is absorbing,
reaching `L` with probability 1 from every state is equivalent to `L` being reachable from every
state. The paper states `w_{ik} > 0` on p. 17 and `w_{Lk} = 0` in Problem 2; the consistent reading
`w_{ik} > 0` for `i ≠ L` is used. `S_R(i)` is `totalCost` in `ℝ≥0∞`; the right-hand sides are
nonnegative reals. -/
theorem total_cost_eq_cycle {S Act : Type*} [Fintype S] [DecidableEq S] [Fintype Act]
    (q : S → Act → S → ℝ) (w : S → Act → ℝ) (L : S) (hq : IsTransitionLaw q)
    (hL : ∀ a, q L a L = 1) (hwL : ∀ a, w L a = 0) (hw : ∀ i a, i ≠ L → 0 < w i a)
    (hB : ∀ D : S → Act → ℝ, IsStationaryRandomized D → ∀ i, ∃ t : ℕ, 0 < (chainMatrix q D ^ t) i L)
    (D : S → Act → ℝ) (hD : IsStationaryRandomized D)
    (D₀ : Act → ℝ) (hD₀ : (∀ a, 0 ≤ D₀ a) ∧ ∑ a, D₀ a = 1)
    (π : Option S → ℝ)
    (hπ : JewellMRP.InfiniteStep.IsStationary (chainMatrix (augLaw q L) (augProc D D₀)) π) :
    0 < π none ∧
    (∀ j, Summable (fun t : ℕ => tabooProb (chainMatrix (augLaw q L) (augProc D D₀)) none t j)) ∧
    (1 / (Fintype.card S : ℝ≥0∞)) * ∑ i, totalCost q w D i =
      ENNReal.ofReal (∑' t : ℕ, ∑ j, tabooProb (chainMatrix (augLaw q L) (augProc D D₀)) none t j *
        ∑ a, augProc D D₀ j a * augCost w j a) ∧
    ∑' t : ℕ, ∑ j, tabooProb (chainMatrix (augLaw q L) (augProc D D₀)) none t j *
        ∑ a, augProc D D₀ j a * augCost w j a =
      (1 / π none) * ∑ j, π j * ∑ a, augProc D D₀ j a * augCost w j a := by sorry

end DermanSeqDecisions.LinProg

