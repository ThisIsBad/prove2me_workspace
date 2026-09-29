import Mathlib
import Definitions.Def_LocalSearchFL_UFL_uflCost

namespace LocalSearchFL.UFL

/-- **Capture** (Definition 3.1, p. 549). Given the assignment `σS` of the clients to the
facilities of a solution `S` and the assignment `σO` to those of a solution `O`, the facility
`s` captures `o` if `s` serves more than half of the clients served by `o`:
`|N^o_s| > ½ |N_O(o)|` with `N^o_s = N_O(o) ∩ N_S(s)`, stated in integers as
`|N_O(o)| < 2 |N^o_s|`. -/
def captures {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl] [DecidableEq Fa]
    (σS σO : Cl → Fa) (s o : Fa) : Prop :=
  (nbhd σO o).card < 2 * (nbhd σO o ∩ nbhd σS s).card

instance {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl] [DecidableEq Fa]
    (σS σO : Cl → Fa) (s o : Fa) : Decidable (captures σS σO s o) := by
  unfold captures; infer_instance

/-- A facility `s` is **good** (p. 549, recalled on p. 555) if it captures no facility of `O`,
and bad otherwise. -/
def IsGood {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl] [DecidableEq Fa]
    (σS σO : Cl → Fa) (O : Finset Fa) (s : Fa) : Prop :=
  ∀ o ∈ O, ¬ captures σS σO s o

/-- The **mapping π of the proof of Lemma 4.2** (p. 555), as one permutation of all clients:
(i) `π` maps every `N_O(o)` onto itself (`σO (π j) = σO j`), i.e. it is a bijection of each
`N_O(o)`; (ii) Property 3.1 (p. 549): if `s` does not capture `o`, then `π(N^o_s) ∩ N^o_s = ∅`;
(iii) the refinement of p. 555: if `s` captures `o`, then every `j ∈ N^o_s` with `π(j) ∈ N^o_s`
satisfies `π(j) = j`. -/
def IsRefinedPi {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl] [DecidableEq Fa]
    (σS σO : Cl → Fa) (π : Equiv.Perm Cl) : Prop :=
  (∀ j, σO (π j) = σO j) ∧
  (∀ s o : Fa, ¬ captures σS σO s o →
    ∀ j ∈ nbhd σO o ∩ nbhd σS s, π j ∉ nbhd σO o ∩ nbhd σS s) ∧
  (∀ s o : Fa, captures σS σO s o →
    ∀ j ∈ nbhd σO o ∩ nbhd σS s, π j ∈ nbhd σO o ∩ nbhd σS s → π j = j)

end LocalSearchFL.UFL
