import Mathlib

namespace OnlineConvexOpt.Introduction

variable {N : ℕ}

/-- Number of mistakes an algorithm's predictions `algPredict` make against the true outcomes
`outcome` on rounds `0, …, T - 1` (Hazan's `M_T`, the book's rounds `1, …, T` shifted down by
one), p. 9. -/
def algMistakes (algPredict outcome : ℕ → Bool) (T : ℕ) : ℕ :=
  ((Finset.range T).filter (fun t => algPredict t ≠ outcome t)).card

/-- Number of mistakes expert `i`'s predictions `expertPredict` make against the true outcomes
`outcome` on rounds `0, …, T - 1` (Hazan's `M_T(i)`), p. 9. -/
def expertMistakes (expertPredict : ℕ → Fin N → Bool) (outcome : ℕ → Bool) (i : Fin N)
    (T : ℕ) : ℕ :=
  ((Finset.range T).filter (fun t => expertPredict t i ≠ outcome t)).card

end OnlineConvexOpt.Introduction
