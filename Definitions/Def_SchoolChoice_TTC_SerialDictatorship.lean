import Mathlib
import Definitions.Def_SchoolChoice_TTC_Algorithm

namespace SchoolChoice.TTC

variable {I S : Type} [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]

/-- One turn of the serial dictatorship: the state is a pair (counters, assignment);
student `i` takes her favourite school under `P i` among the schools with a positive
counter, whose counter then drops by one. If no school has a seat left, nothing changes. -/
def sdTurn (P : I → Pref S) (acc : (S → ℕ) × (I → Option S)) (i : I) :
    (S → ℕ) × (I → Option S) :=
  match bestIn (P i) (Finset.univ.filter (fun s => 0 < acc.1 s)) with
  | none => acc
  | some s => (Function.update acc.1 s (acc.1 s - 1), Function.update acc.2 i (some s))

/-- The serial dictatorship induced by the priority ordering `π` (Section II.B, p. 16):
the student ranked first by `π` is assigned her top choice, the next student her top
choice among the remaining seats, and so on, starting from the capacities `q`. The value
`none` would mean that a student found no seat left. -/
def serialDictatorship (q : S → ℕ) (π : Priority I) (P : I → Pref S) : I → Option S :=
  (((List.finRange (Fintype.card I)).map π.symm).foldl (sdTurn P) (q, fun _ => none)).2

end SchoolChoice.TTC
