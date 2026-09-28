import Mathlib

namespace SocialEquilibrium.Existence

/-- Debreu (1952), p. 888–889: the *graph* of a multi-valued function `φ`, which associates
with each `z ∈ Z` a subset `φ z ⊆ W`, is the set `{(z, w) | w ∈ φ z} ⊆ Z × W`. -/
def graph {Z W : Type*} (φ : Z → Set W) : Set (Z × W) :=
  {p | p.2 ∈ φ p.1}

/-- Debreu (1952), p. 889: a multi-valued function is *semicontinuous* if its graph is
closed. -/
def IsSemicontinuous {Z W : Type*} [TopologicalSpace Z] [TopologicalSpace W]
    (φ : Z → Set W) : Prop :=
  IsClosed (graph φ)

end SocialEquilibrium.Existence
