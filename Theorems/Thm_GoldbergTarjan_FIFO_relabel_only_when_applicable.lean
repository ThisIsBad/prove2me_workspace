import Mathlib
import Definitions.Def_GoldbergTarjan_FIFO_Network
import Definitions.Def_GoldbergTarjan_FIFO_PushRelabel
import Definitions.Def_GoldbergTarjan_FIFO_Algorithm
import Definitions.Def_GoldbergTarjan_FIFO_Counts

namespace GoldbergTarjan.FIFO

/-- Lemma 4.1 (Goldberg–Tarjan 1988, p. 929): the push/relabel operation does a relabeling only
when the relabeling operation is applicable. In every run of the first-in, first-out algorithm,
whenever the `j`-th push/relabel operation of the `k`-th discharge (of the front vertex `v`)
takes the relabeling branch of Fig. 3, `relabel(v)` is applicable (Fig. 1) at that moment. -/
theorem relabel_only_when_applicable {V : Type} [Fintype V] [DecidableEq V]
    (N : Network V) (L : V → List V) (K : ℕ) (S : ℕ → State V) (J : ℕ → ℕ)
    (hrun : IsFIFORun N L K S J) (k : ℕ) (hk : k < K) (j : ℕ) (hj : j < J k)
    (hrel : IsRelabelOp N L (frontVertex N (S k))
      (prIter N L (frontVertex N (S k)) (S k).cfg j)) :
    RelabelApplicable N (prIter N L (frontVertex N (S k)) (S k).cfg j).f
      (prIter N L (frontVertex N (S k)) (S k).cfg j).d (frontVertex N (S k)) := by sorry

end GoldbergTarjan.FIFO

