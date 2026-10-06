import Mathlib
import Definitions.Def_AKSSorting_Core_IsExpander

namespace AlonExpanders.Core

/-- `(n, d, c)`-magnifier (Alon, *Eigenvalues and expanders*, Combinatorica 6 (1986), §2, p. 85):
a graph `G` on `n` vertices with maximal degree (at most) `d` such that every set `X` of vertices
with `|X| ≤ n/2` satisfies `|N(X) − X| ≥ c · |X|`, where `N(X) = AKSSorting.Core.neighbours G X`.
The condition `|X| ≤ n/2` is written `2 * |X| ≤ n` (no natural-number division). -/
def IsMagnifier {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (n d : ℕ) (c : ℝ) : Prop :=
  Fintype.card V = n ∧ G.maxDegree ≤ d ∧
    ∀ X : Finset V, 2 * X.card ≤ n →
      c * (X.card : ℝ) ≤ ((AKSSorting.Core.neighbours G X \ (X : Set V)).ncard : ℝ)

end AlonExpanders.Core
