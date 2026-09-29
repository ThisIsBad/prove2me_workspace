import Mathlib

namespace SchoolChoice.TTCQuota

/-- A strict preference of a student over all schools, encoded as a ranking:
`p s` is the rank of school `s`, rank `0` is the favourite. Since `p` is a bijection
onto `Fin (card S)`, ties are impossible and every school is ranked
(Abdulkadiroğlu–Sönmez 2003, Section I, p. 8). "`a` is weakly preferred to `b`"
is `p a ≤ p b`; "`a` is strictly preferred to `b`" is `p a < p b`. -/
abbrev Pref (S : Type) [Fintype S] : Type := S ≃ Fin (Fintype.card S)

/-- A strict priority ordering of a school over all students, encoded as a ranking:
`r i` is the rank of student `i`, rank `0` is the highest priority (Section I, p. 8). -/
abbrev Priority (I : Type) [Fintype I] : Type := I ≃ Fin (Fintype.card I)

variable {I S Ty : Type} [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]
  [Fintype Ty] [DecidableEq Ty]

/-- The rank of a possibly empty assignment `o : Option S` under the preference `p`:
`some s` has rank `p s < card S`, and `none` (no school) has rank `card S`, so being
unassigned is strictly worse than every school. "`a` is weakly better than `b`" is
`orank p a ≤ orank p b`, "strictly better" is `orank p a < orank p b`. -/
def orank (p : Pref S) : Option S → ℕ
  | some s => (p s : ℕ)
  | none => Fintype.card S

/-- The controlled choice constraints (Section III, pp. 19–22) for a (possibly partial)
assignment `ν : I → Option S` of schools to students, where `τ i` is the type of student
`i`, `q s` is the capacity of school `s` and `qt s t` is the quota of school `s` for
students of type `t`: every school `s` is assigned to at most `q s` students, and to at
most `qt s t` students of each type `t`. -/
def SatisfiesCC (q : S → ℕ) (qt : S → Ty → ℕ) (τ : I → Ty) (ν : I → Option S) : Prop :=
  ∀ s, (Finset.univ.filter (fun i => ν i = some s)).card ≤ q s ∧
    ∀ t, (Finset.univ.filter (fun i => ν i = some s ∧ τ i = t)).card ≤ qt s t

/-- Constrained efficiency (Section III.B, pp. 22–23) of an assignment `μ` with respect to
the preference profile `P`: `μ` satisfies the controlled choice constraints, and there is
no other assignment `ν` satisfying them which assigns every student a weakly better
school and at least one student a strictly better school (being unassigned, `none`, is
worse than every school). -/
def IsConstrainedEfficient (q : S → ℕ) (qt : S → Ty → ℕ) (τ : I → Ty) (P : I → Pref S)
    (μ : I → Option S) : Prop :=
  SatisfiesCC q qt τ μ ∧
    ¬ ∃ ν : I → Option S, SatisfiesCC q qt τ ν ∧
      (∀ i, orank (P i) (ν i) ≤ orank (P i) (μ i)) ∧ ∃ i, orank (P i) (ν i) < orank (P i) (μ i)

end SchoolChoice.TTCQuota
