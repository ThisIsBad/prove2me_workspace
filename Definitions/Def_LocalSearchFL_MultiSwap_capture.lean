import Mathlib

namespace LocalSearchFL.MultiSwap

/-- The **neighbourhood** `N_A(a)` of a facility `a` under an assignment `σ` of clients to
facilities (p. 548): the set of clients that `a` serves. -/
def nbhd {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl] [DecidableEq Fa] (σ : Cl → Fa) (a : Fa) : Finset Cl :=
  Finset.univ.filter (fun j => σ j = a)

/-- The neighbourhood `N_A(T) = ⋃_{a ∈ T} N_A(a)` of a set `T` of facilities (p. 548): the set of
clients served by some facility of `T`. -/
def nbhdSet {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl] [DecidableEq Fa] (σ : Cl → Fa) (T : Finset Fa) :
    Finset Cl :=
  Finset.univ.filter (fun j => σ j ∈ T)

/-- **Capture of a set** (§3.4, p. 551). Given the assignment `σS` of the clients to the
facilities of a solution `S` and the assignment `σO` to those of a solution `O`,
`capture(A) = {o ∈ O | |N_S(A) ∩ N_O(o)| > |N_O(o)|/2}`, stated in integers as
`|N_O(o)| < 2 |N_S(A) ∩ N_O(o)|`. -/
def capture {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl] [DecidableEq Fa]
    (σS σO : Cl → Fa) (O A : Finset Fa) : Finset Fa :=
  O.filter (fun o => (nbhd σO o).card < 2 * (nbhdSet σS A ∩ nbhd σO o).card)

/-- A facility `s` is **good** (p. 549) if it captures no facility of `O`, i.e.
`capture({s}) = ∅`, and **bad** otherwise (Definition 3.1: `s` captures `o` iff
`|N_S(s) ∩ N_O(o)| > ½ |N_O(o)|`). -/
def IsGood {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl] [DecidableEq Fa]
    (σS σO : Cl → Fa) (O : Finset Fa) (s : Fa) : Prop :=
  capture σS σO O {s} = ∅

end LocalSearchFL.MultiSwap
