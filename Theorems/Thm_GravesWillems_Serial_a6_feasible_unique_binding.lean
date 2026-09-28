import Mathlib
import Definitions.Def_GravesWillems_Serial_programP

namespace GravesWillems.Serial

/-- Appendix, proof of the Result (Graves–Willems 2000, pp. 81–82): if `D(0) = 0` and `D` is
nondecreasing, the vector (A6) is nonnegative and satisfies every constraint (A3) with equality,
hence is feasible for `P*`; and every base-stock vector satisfying all constraints (A3) with
equality coincides with (A6) on stages `1, …, N`. -/
theorem a6_feasible_unique_binding (N : ℕ) (T : ℕ → ℕ) (D : ℕ → ℝ)
    (hD0 : D 0 = 0) (hD : Monotone D) :
    Feasible N T D (a6 N T D) ∧
    (∀ i ∈ Finset.Icc 1 N,
      ∑ m ∈ Finset.Icc 1 i, a6 N T D m = D (∑ m ∈ Finset.Icc 1 i, T m)) ∧
    ∀ B : ℕ → ℝ,
      (∀ i ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 i, B m = D (∑ m ∈ Finset.Icc 1 i, T m)) →
      ∀ i ∈ Finset.Icc 1 N, B i = a6 N T D i := by sorry

end GravesWillems.Serial
