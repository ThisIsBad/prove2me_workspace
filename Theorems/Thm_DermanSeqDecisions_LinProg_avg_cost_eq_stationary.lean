import Mathlib
import Definitions.Def_JewellMRP_InfiniteStep_Model
import Definitions.Def_DermanSeqDecisions_LinProg_Model

open Matrix

namespace DermanSeqDecisions.LinProg

/-- (6), p. 20 (Derman, *On Sequential Decisions and Markov Chains*, Management Science 9(1):16–24 (1962), DOI 10.1287/mnsc.9.1.16, §3, proof of Theorem 2, display (6)).

Problem 1 under Assumption A: the chance laws `q_{ij}(k)` are stochastic, the costs `w_{ik}` are
positive, and for every procedure of `C′` the states form one class. Then for every `D ∈ C′` and
its stationary vector `π` (the unique solution of (5) for `p_{ij} = ∑_k q_{ij}(k) D_{ik}`),
`Q_R(i) = ∑_j π_j ∑_k D_{jk} w_{jk}` for every initial state `i`.

**Formalization Note.** Assumption A is `∀ D ∈ C′, (chainMatrix q D).IsIrreducible`; with stochastic
`q` and `D` the chain matrix is row-stochastic, so this is Derman's "the states `0, ⋯, L` belong
to the same class". `Q_R(i)` is `avgCost`, the real `limsup` of `(1/T) ∑_{t=0}^T W_t`
(a bounded sequence). -/
theorem avg_cost_eq_stationary {S Act : Type*} [Fintype S] [DecidableEq S] [Fintype Act]
    (q : S → Act → S → ℝ) (w : S → Act → ℝ) (hq : IsTransitionLaw q)
    (hw : ∀ i a, 0 < w i a)
    (hA : ∀ D : S → Act → ℝ, IsStationaryRandomized D → (chainMatrix q D).IsIrreducible)
    (D : S → Act → ℝ) (hD : IsStationaryRandomized D)
    (π : S → ℝ) (hπ : JewellMRP.InfiniteStep.IsStationary (chainMatrix q D) π) :
    ∀ i, avgCost q w D i = ∑ j, π j * ∑ a, D j a * w j a := by sorry

end DermanSeqDecisions.LinProg

