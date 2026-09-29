import Mathlib
import Definitions.Def_LocalSearchFL_KMedian_kmCost

namespace LocalSearchFL.KMedian

/-- **Capture** (Definition 3.1, p. 549). Given the assignment `σS` of the clients to the
facilities of a solution `S` and the assignment `σO` to those of a solution `O`, the facility
`s` captures `o` if `s` serves more than half of the clients served by `o`:
`|N^o_s| > ½ |N_O(o)|` with `N^o_s = N_O(o) ∩ N_S(s)`, stated in integers as
`|N_O(o)| < 2 |N^o_s|`. -/
def captures {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl] [DecidableEq Fa]
    (σS σO : Cl → Fa) (s o : Fa) : Prop :=
  (nbhd σO o).card < 2 * (nbhd σO o ∩ nbhd σS s).card

/-- A facility `s` is **good** (p. 549) if it captures no facility of `O`, and bad otherwise. -/
def IsGood {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl] [DecidableEq Fa]
    (σS σO : Cl → Fa) (O : Finset Fa) (s : Fa) : Prop :=
  ∀ o ∈ O, ¬ captures σS σO s o

end LocalSearchFL.KMedian
