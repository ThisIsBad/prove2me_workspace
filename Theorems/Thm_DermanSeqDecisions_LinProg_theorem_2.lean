import Mathlib
import Definitions.Def_DermanSeqDecisions_LinProg_LinearFractional
import Definitions.Def_DermanSeqDecisions_LinProg_Model

open Matrix

namespace DermanSeqDecisions.LinProg

/-- Theorem 2, p. 20 (Derman, *On Sequential Decisions and Markov Chains*, Management Science 9(1):16–24 (1962), DOI 10.1287/mnsc.9.1.16, §3, Theorem 2), pinned-down reading following its proof (pp. 20–23).
The printed statement is "If Assumption A (B) holds, then problem 1 (2) can be formulated as a linear
programming problem."

Let the chance laws `q_{ij}(k)` on the states `0, ⋯, L` and decisions `d_1, ⋯, d_K` be stochastic.

**Problem 1.** If `w_{ik} > 0` and Assumption A holds (for every procedure of `C′` the states form
one class), then the linear program "minimize (8), `∑_{j,k} x_{jk} w_{jk}`, subject to (10)" has an
optimal solution, and for every optimal solution `x*`: `∑_k x*_{jk} > 0` for all `j`, the
procedure `D*_{jk} = x*_{jk} / ∑_k x*_{jk}` belongs to `C′`, and `Q_{D*}(i) ≤ Q_D(i)` for every
`D ∈ C′` and every `i`.

**Problem 2.** If `L` is absorbing under every decision, `w_{Lk} = 0`, `w_{ik} > 0` for `i ≠ L`,
and Assumption B holds, adjoin the state `−1` as on p. 21 and apply the Lemma to (9) subject to the
augmented (10). The linear program "minimize `h(z) = ∑_{j,k} w_{jk} z_{jk}` subject to (12)" has an
optimal solution, and for every optimal `(z*, z*_{n+1})`: `z*_{n+1} > 0`, and with
`x* = z*/z*_{n+1}` the procedure `D*_{jk} = x*_{jk} / ∑_k x*_{jk}` (`j = 0, ⋯, L`) belongs to
`C′` and satisfies `S_{D*}(i) ≤ S_D(i)` for every `D ∈ C′` and every `i`.

**Formalization Note.** Optimality is over `C′` (the class Theorem 2 concerns; optimality over all of
`C` is Theorem 1). Assumption A is irreducibility of every chain matrix of `C′`; Assumption B is
reachability of `L` (equivalent to absorption with probability 1 for a finite chain with `L`
absorbing). The program (12) is written with the Lemma's `IsFeasible12` for the data of the
augmented (10): coefficient matrix `freqRowMatrix (augLaw q L)`, right-hand side `freqRhs`,
denominator `cycleDenom` (`d_{(−1,k)} = 1`, else `0`) and costs `cycleCost w`
(`w_{−1,k} = 0`). The two problems carry their own cost hypotheses, which conflict at `L`. -/
theorem theorem_2 {S Act : Type*} [Fintype S] [DecidableEq S] [Nonempty S] [Fintype Act]
    [Nonempty Act] (q : S → Act → S → ℝ) (w : S → Act → ℝ) (hq : IsTransitionLaw q) :
    ((∀ i a, 0 < w i a) →
      (∀ D : S → Act → ℝ, IsStationaryRandomized D → (chainMatrix q D).IsIrreducible) →
      (∃ x : S → Act → ℝ, IsFreqSolution q x ∧
        ∀ x' : S → Act → ℝ, IsFreqSolution q x' → freqObjective w x ≤ freqObjective w x') ∧
      ∀ x : S → Act → ℝ, IsFreqSolution q x →
        (∀ x' : S → Act → ℝ, IsFreqSolution q x' → freqObjective w x ≤ freqObjective w x') →
        (∀ j, 0 < ∑ k, x j k) ∧ IsStationaryRandomized (decode x) ∧
        ∀ D : S → Act → ℝ, IsStationaryRandomized D →
          ∀ i, avgCost q w (decode x) i ≤ avgCost q w D i) ∧
    (∀ L : S, (∀ a, q L a L = 1) → (∀ a, w L a = 0) → (∀ i a, i ≠ L → 0 < w i a) →
      (∀ D : S → Act → ℝ, IsStationaryRandomized D →
        ∀ i, ∃ t : ℕ, 0 < (chainMatrix q D ^ t) i L) →
      (∃ (z : Option S × Act → ℝ) (zlast : ℝ),
        IsFeasible12 (freqRowMatrix (augLaw q L)) freqRhs cycleDenom z zlast ∧
        ∀ (z' : Option S × Act → ℝ) (zlast' : ℝ),
          IsFeasible12 (freqRowMatrix (augLaw q L)) freqRhs cycleDenom z' zlast' →
          linObj (cycleCost w) z ≤ linObj (cycleCost w) z') ∧
      ∀ (z : Option S × Act → ℝ) (zlast : ℝ),
        IsFeasible12 (freqRowMatrix (augLaw q L)) freqRhs cycleDenom z zlast →
        (∀ (z' : Option S × Act → ℝ) (zlast' : ℝ),
          IsFeasible12 (freqRowMatrix (augLaw q L)) freqRhs cycleDenom z' zlast' →
          linObj (cycleCost w) z ≤ linObj (cycleCost w) z') →
        0 < zlast ∧ IsStationaryRandomized (decodeCycle z zlast) ∧
        ∀ D : S → Act → ℝ, IsStationaryRandomized D →
          ∀ i, totalCost q w (decodeCycle z zlast) i ≤ totalCost q w D i) := by sorry

end DermanSeqDecisions.LinProg

