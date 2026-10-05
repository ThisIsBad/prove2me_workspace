import Mathlib
import Definitions.Def_JewellMRP_InfiniteStep_Model
import Definitions.Def_DermanSeqDecisions_LinProg_Model

open Matrix

namespace DermanSeqDecisions.LinProg

/-- §3, p. 21 (Derman, *On Sequential Decisions and Markov Chains*, Management Science 9(1):16–24 (1962), DOI 10.1287/mnsc.9.1.16, §3, proof of Theorem 2, the paragraph after (10), unnumbered).

Let `I` be a finite state set with stochastic chance laws `q_{ij}(k)`, and suppose that for every
procedure of `C′` the states of `I` belong to the same class. Then:
1. for every `D ∈ C′` and its stationary vector `π` (5), `x_{jk} = π_j D_{jk}` solves (10) and
   `∑_k x_{jk} > 0` for every `j ∈ I`;
2. every solution `x` of (10) has `∑_k x_{jk} > 0` for every `j ∈ I`; the procedure
   `D_{jk} = x_{jk} / ∑_k x_{jk}` belongs to `C′`, its stationary vector is `π_j = ∑_k x_{jk}`, and
   `x_{jk} = π_j D_{jk}`, so `x` is the solution of (10) that corresponds to it.

**Formalization Note.** The statement is generic in the state set `I`, as the paper uses it twice:
`I = {0, ⋯, L}` under Assumption A, and `I = {−1, 0, ⋯, L}` with the augmented law of Problem 2.
"Same class" is `Matrix.IsIrreducible` of the (row-stochastic) chain matrix. -/
theorem freq_solution_correspondence {I Act : Type*} [Fintype I] [DecidableEq I] [Fintype Act]
    (q : I → Act → I → ℝ) (hq : IsTransitionLaw q)
    (hA : ∀ D : I → Act → ℝ, IsStationaryRandomized D → (chainMatrix q D).IsIrreducible) :
    (∀ D : I → Act → ℝ, IsStationaryRandomized D → ∀ π : I → ℝ,
      JewellMRP.InfiniteStep.IsStationary (chainMatrix q D) π →
      IsFreqSolution q (fun j k => π j * D j k) ∧ ∀ j, 0 < ∑ k, π j * D j k) ∧
    ∀ x : I → Act → ℝ, IsFreqSolution q x →
      (∀ j, 0 < ∑ k, x j k) ∧ IsStationaryRandomized (decode x) ∧
      JewellMRP.InfiniteStep.IsStationary (chainMatrix q (decode x)) (fun j => ∑ k, x j k) ∧
      ∀ j k, x j k = (∑ k', x j k') * decode x j k := by sorry

end DermanSeqDecisions.LinProg

