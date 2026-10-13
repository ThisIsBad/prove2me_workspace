import Definitions.Def_TopkisRation_Myopic_MultiPeriod

namespace TopkisRation.Myopic

variable {n : ℕ}

/-- Equation (20), pp. 175–176: comparison of actual and myopic period costs. -/
theorem eq_20 (Q : MultiModel n) (hQ : Q.Standing)
    (m : ℕ) (hm2 : 2 ≤ m) (hmN : m ≤ Q.N)
    (x : ℝ) (hx : 0 ≤ x)
    (hmin : ∀ z, 0 ≤ z → Q.gtilde m x ≤ Q.gtilde m z) :
    (∀ z, 0 ≤ z → z ≤ x →
      Q.gtilde (m - 1) z = Q.gmyopic (m - 1) z + Q.C m x) ∧
    ∀ z, x ≤ z →
      Q.gmyopic (m - 1) z + Q.C m x ≤ Q.gtilde (m - 1) z := by sorry

end TopkisRation.Myopic

