import Mathlib
import Definitions.Def_EdmondsKarp_Scaling_Transport
import Definitions.Def_EdmondsKarp_Scaling_Augmentation

namespace EdmondsKarp.Scaling

variable {m n : ℕ}

/-- Problem `p` of the scaling method (§2.2, p. 259): the same nodes, arcs and costs `d` as the
given transportation problem with integral capacities `a`, `b`, but with capacity `[a_i / 2^p]` on
`(s, s_i)` and `[b_j / 2^p]` on `(t_j, t)` (`[x]` = greatest integer `≤ x`, footnote 3; for natural
numbers this is `ℕ` division). Problem `0` is the original problem. -/
def problem (a : Fin m → ℕ) (b : Fin n → ℕ) (d : Fin m → Fin n → ℝ) (p : ℕ) : Transport m n where
  a i := ((a i / 2 ^ p : ℕ) : ℝ)
  b j := ((b j / 2 ^ p : ℕ) : ℝ)
  d := d

/-- A run of the scaling method (§2.2, pp. 259–260) with `l` phases, for Problems `l-1, l-2, …, 0`.
Phase `p < l` is the sequence of flows `F p 0, …, F p (K p)` of Problem `p`, with `K p` flow
augmentations:
* the initial flow in Problem `l - 1` is `0`;
* for `1 ≤ p < l`, the initial flow in Problem `p - 1` is `2 • F p (K p)`;
* each `F p (k+1)` is obtained from `F p k` by one augmentation in Problem `p`;
* every flow of phase `p` is pseudo-extreme in Problem `p` (the invariant the paper states for the
  method's choice of augmenting paths);
* the phase ends at a flow admitting no augmenting path in Problem `p`. -/
structure IsScalingRun (a : Fin m → ℕ) (b : Fin n → ℕ) (d : Fin m → Fin n → ℝ) (l : ℕ)
    (K : ℕ → ℕ) (F : ℕ → ℕ → Flow m n) : Prop where
  start : F (l - 1) 0 = 0
  restart : ∀ p, 1 ≤ p → p < l → F (p - 1) 0 = (2 : ℝ) • F p (K p)
  step : ∀ p, p < l → ∀ k, k < K p → AugStep (problem a b d p) (F p k) (F p (k + 1))
  pseudo : ∀ p, p < l → ∀ k, k ≤ K p → IsPseudoExtreme (problem a b d p) (F p k)
  stop : ∀ p, p < l → ¬ ∃ L, IsAugPath (problem a b d p) (F p (K p)) L

end EdmondsKarp.Scaling
