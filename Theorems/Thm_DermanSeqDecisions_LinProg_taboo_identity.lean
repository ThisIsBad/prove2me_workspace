import Mathlib
import Definitions.Def_JewellMRP_InfiniteStep_Model
import Definitions.Def_DermanSeqDecisions_LinProg_Model

open Matrix

namespace DermanSeqDecisions.LinProg

/-- (4), p. 20 (Derman, *On Sequential Decisions and Markov Chains*, Management Science 9(1):16–24 (1962), DOI 10.1287/mnsc.9.1.16, §3, display (4), unnumbered result quoted from Chung).

Let `P` be the transition matrix of a Markov chain with finite state set `I`, all states belonging
to the same class (`P` row-stochastic and irreducible), let `π` be its stationary vector (5), let
`f : I → ℝ` and `i ∈ I`. Then for every `j` the taboo probabilities `_i p^{(t)}_{ij}` are summable
in `t`, the series `∑_t ∑_j _i p^{(t)}_{ij} f(j)` converges to `∑_j ∑_t _i p^{(t)}_{ij} f(j)`, and that
value equals `(1/π_i) ∑_j π_j f(j)`.

**Formalization Note.** "All states belonging to the same class" is
`JewellMRP.InfiniteStep.IsErgodic P` (row-stochastic and `Matrix.IsIrreducible`; periodic chains
are allowed). The summability of the taboo series is part of the conclusion, so no `tsum` takes a
junk value. -/
theorem taboo_identity {I : Type*} [Fintype I] [DecidableEq I]
    (P : Matrix I I ℝ) (hP : JewellMRP.InfiniteStep.IsErgodic P)
    (π : I → ℝ) (hπ : JewellMRP.InfiniteStep.IsStationary P π) (f : I → ℝ) (i : I) :
    (∀ j, Summable (fun t : ℕ => tabooProb P i t j)) ∧
    HasSum (fun t : ℕ => ∑ j, tabooProb P i t j * f j) (∑ j, ∑' t : ℕ, tabooProb P i t j * f j) ∧
    ∑ j, ∑' t : ℕ, tabooProb P i t j * f j = (1 / π i) * ∑ j, π j * f j := by sorry

end DermanSeqDecisions.LinProg

