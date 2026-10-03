import Mathlib

/-!
Scalar multiplication of an `R ∪ {+∞}`-value by a nonnegative real, used to state the Lovász
extension (Eq. (4.6)) and convexity of an extended-real-valued function (Theorem 4.16), in
`DiscreteConvex.MConvexSetsB`.
-/

namespace DiscreteConvex.MConvexSetsB

/-- The scalar multiple `c • x` of `x ∈ R ∪ \{+∞\}` by `c ∈ R`, with the convention `c • ⊤ = ⊤`
for `c ≠ 0` and `0 • ⊤ = 0`. Every use of this operation in this mission has `c ≥ 0` (a
difference of consecutive sorted values, or a convex-combination weight in `[0,1]`). -/
noncomputable def ScalarWithTop (c : ℝ) (x : WithTop ℝ) : WithTop ℝ :=
  match x with
  | ⊤ => if c = 0 then (0 : WithTop ℝ) else ⊤
  | (r : ℝ) => ((c * r : ℝ) : WithTop ℝ)

end DiscreteConvex.MConvexSetsB
