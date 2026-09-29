import Mathlib

namespace ChvatalPolytopes.Perfect

/-- **Duplication of a vertex** (Chvátal 1975, p. 140): the graph obtained from `G` by adding a
new vertex `u'` and joining it by edges to all the neighbours of `u`, but not to `u` itself.
The vertex set is `Option V`: `some v` is the old vertex `v` and `none` is the new vertex `u'`.
Old vertices keep their adjacencies; `u'` is adjacent to `some w` exactly when `G.Adj u w`. -/
def duplicate {V : Type*} (G : SimpleGraph V) (u : V) : SimpleGraph (Option V) where
  Adj x y :=
    match x, y with
    | some v, some w => G.Adj v w
    | none, some w => G.Adj u w
    | some v, none => G.Adj v u
    | none, none => False
  symm := ⟨by
    intro x y h
    cases x <;> cases y <;> simp_all [G.adj_comm]⟩
  loopless := ⟨by
    intro x h
    cases x <;> simp_all⟩

end ChvatalPolytopes.Perfect
