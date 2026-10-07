import Mathlib

namespace FreedmanTail.Bernstein

/-- Freedman (1975), (3.1) Lemma, p. 106: `g(0) = 1/2`, `g(x) = (e^x − 1 − x)/x²` for `x ≠ 0`
is (strictly) increasing. -/
theorem lemma_3_1 :
    StrictMono (fun x : ℝ => if x = 0 then (1 / 2 : ℝ) else (Real.exp x - 1 - x) / x ^ 2) := by sorry

end FreedmanTail.Bernstein

