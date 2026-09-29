import Mathlib

namespace ChvatalPolytopes.Separation

/-- **Cutset** (the notion used in the proof of Corollary 4.3, Chvátal 1975, p. 144): a vertex
set `K` of `G` is a *cutset* if there are two vertices `x, y` outside `K` that are not joined by
any path of `G − K`, the subgraph of `G` induced on the complement of `K`.

Equivalently, `G = G₁ ∪ G₂` with `V₁ ∩ V₂ = K`, `V₁ − V₂ ≠ ∅`, `V₂ − V₁ ≠ ∅` and no edge
between `V₁ − V₂` and `V₂ − V₁`. In particular `K = V` is never a cutset. -/
def IsCutset {V : Type*} (G : SimpleGraph V) (K : Set V) : Prop :=
  ∃ (x y : V) (hx : x ∉ K) (hy : y ∉ K),
    ¬ (G.induce Kᶜ).Reachable ⟨x, hx⟩ ⟨y, hy⟩

end ChvatalPolytopes.Separation
