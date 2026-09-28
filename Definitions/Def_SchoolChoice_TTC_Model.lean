import Mathlib

namespace SchoolChoice.TTC

/-- A strict preference of a student over all schools, encoded as a ranking:
`p s` is the rank of school `s`, rank `0` is the favourite. Since `p` is a bijection
onto `Fin (card S)`, ties are impossible and every school is ranked
(Abdulkadiroğlu–Sönmez 2003, Section I, p. 8). "`a` is weakly preferred to `b`"
is `p a ≤ p b`; "`a` is strictly preferred to `b`" is `p a < p b`. -/
abbrev Pref (S : Type) [Fintype S] : Type := S ≃ Fin (Fintype.card S)

/-- A strict priority ordering of a school over all students, encoded as a ranking:
`r i` is the rank of student `i`, rank `0` is the highest priority (Section I, p. 8). -/
abbrev Priority (I : Type) [Fintype I] : Type := I ≃ Fin (Fintype.card I)

variable {I S : Type} [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]

/-- A matching (Section I, p. 8): every student is assigned exactly one school
(`μ : I → S`) and no school `s` is assigned to more students than its capacity `q s`. -/
def IsMatching (q : S → ℕ) (μ : I → S) : Prop :=
  ∀ s, (Finset.univ.filter (fun i => μ i = s)).card ≤ q s

/-- Pareto efficiency of a matching `μ` with respect to the preference profile `P`
(Section I, p. 8): there is no other matching `ν` (capacity-respecting) that assigns
every student a weakly better school and at least one student a strictly better school. -/
def IsParetoEfficient (q : S → ℕ) (P : I → Pref S) (μ : I → S) : Prop :=
  ¬ ∃ ν : I → S, IsMatching q ν ∧ (∀ i, P i (ν i) ≤ P i (μ i)) ∧ ∃ i, P i (ν i) < P i (μ i)

end SchoolChoice.TTC
