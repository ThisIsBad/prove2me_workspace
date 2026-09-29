import Mathlib
import Definitions.Def_EdmondsKarp_MaxCapacity_Network
import Definitions.Def_EdmondsKarp_MaxCapacity_Augmentation
import Definitions.Def_EdmondsKarp_MaxCapacity_Run

namespace EdmondsKarp.MaxCapacity

/-- **Theorem 2** (Edmonds–Karp 1972, p. 253). Let `N` be a network with integer capacities and let
`M > 1` be an integer such that every partition of the nodes into `X ∋ s` and `X̄ ∋ t` has at most `M`
arcs of `N` with one end in `X` and the other in `X̄`; let `f*(t, s)` be the value of a maximum flow.
If the labeling method, started from an integer-valued flow `f^0`, performs `K` augmentations, each
along an augmenting path giving the maximum possible augmentation, then
(a) `K ≤ 1 + log_{M/(M−1)} f*(t, s)`, and
(b) if there is no augmenting path relative to `f^K`, then `f^K` is a maximum flow. -/
theorem maximum_augmentation_bound {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (hcap : IntegralCaps N) (M : ℕ) (hM : 1 < M) (hcross : CrossArcsBounded N M)
    (g : V → V → ℝ) (hg : IsMaxFlow N g)
    (K : ℕ) (f : ℕ → V → V → ℝ) (P : ℕ → List V) (hrun : IsMaxAugRun N K f P)
    (hint : IsIntegralOn N (f 0)) :
    (K : ℝ) ≤ 1 + Real.logb ((M : ℝ) / ((M : ℝ) - 1)) (g N.t N.s) ∧
      ((¬ ∃ Q : List V, IsAugPath N (f K) Q) → IsMaxFlow N (f K)) := by sorry

end EdmondsKarp.MaxCapacity
