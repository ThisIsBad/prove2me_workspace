import Mathlib

namespace ChvatalPolytopes.SeriesParallel

/-- `G` **contains a homeomorph of `K₄`** (Chvátal 1975, p. 150): `G` has a subgraph obtained
from `K₄` by subdividing its edges into paths by inserting new vertices of degree two.

Encoding: there are four distinct *branch vertices* `b 0, b 1, b 2, b 3` and, for each of the six
pairs `i < j`, a path `p i j` in `G` from `b i` to `b j` such that
* no path passes through a branch vertex other than its two endpoints, and
* two different paths share no vertex other than branch vertices (hence, by the previous
  condition, only common endpoints).
The walks `p i j` with `i ≥ j` are not used. `K₄` itself (every path a single edge) counts. -/
def ContainsK4Homeomorph {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (b : Fin 4 → V) (p : ∀ i j : Fin 4, G.Walk (b i) (b j)),
    Function.Injective b ∧
    (∀ i j : Fin 4, i < j → (p i j).IsPath) ∧
    (∀ i j : Fin 4, i < j → ∀ k : Fin 4, b k ∈ (p i j).support → k = i ∨ k = j) ∧
    (∀ i j i' j' : Fin 4, i < j → i' < j' → (i, j) ≠ (i', j') →
      ∀ v : V, v ∈ (p i j).support → v ∈ (p i' j').support → ∃ k : Fin 4, v = b k)

/-- A **series-parallel network** (Chvátal 1975, p. 150): a graph which contains no homeomorph
of `K₄` (as a subgraph, not necessarily induced). -/
def IsSeriesParallel {V : Type*} (G : SimpleGraph V) : Prop :=
  ¬ ContainsK4Homeomorph G

end ChvatalPolytopes.SeriesParallel
