import Mathlib

namespace AKSSorting.Core

/-- `Γ_X`: the set of vertices adjacent to some vertex of `X`. -/
def neighbours {V : Type} (G : SimpleGraph V) (X : Finset V) : Set V :=
  {v | ∃ x ∈ X, G.Adj x v}

/-- `G` is a `⟨k, ε⟩` expander on `⟨A, B⟩` (Ajtai–Komlós–Szemerédi 1983, Definition 2.2, p. 6):
`A` and `B` are disjoint, every edge of `G` joins a vertex of `A` to a vertex of `B` (so no edge
lies inside `A` or inside `B` and no vertex outside `A ∪ B` has an edge), every vertex has at most
`k` neighbours, and for every **nonempty** `X ⊆ A` and every **nonempty** `Y ⊆ B`
`|Γ_X| > (1-ε)(1/ε) min{|X|, ε|B|}` and `|Γ_Y| > (1-ε)(1/ε) min{|Y|, ε|A|}`.

Correction to the page: the paper requires the inequalities for all `X ⊆ A`, including `X = ∅`,
where both sides are `0` and the strict inequality fails; as printed no graph would be an
expander. The conditions are therefore imposed on nonempty sets only. -/
def IsExpander {V : Type} (G : SimpleGraph V) (A B : Finset V) (k : ℕ) (ε : ℝ) : Prop :=
  Disjoint A B ∧
  (∀ u v, G.Adj u v → (u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A)) ∧
  (∀ v, (G.neighborSet v).encard ≤ (k : ℕ∞)) ∧
  (∀ X ⊆ A, X.Nonempty →
    (1 - ε) * (1 / ε) * min (X.card : ℝ) (ε * B.card) < ((neighbours G X).ncard : ℝ)) ∧
  (∀ Y ⊆ B, Y.Nonempty →
    (1 - ε) * (1 / ε) * min (Y.card : ℝ) (ε * A.card) < ((neighbours G Y).ncard : ℝ))

end AKSSorting.Core
