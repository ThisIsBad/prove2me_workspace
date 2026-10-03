import Mathlib
import Definitions.Def_Lubbecke2005_Discretization_Polyhedron

namespace Lubbecke2005.Discretization

/-- **Lübbecke–Desrosiers 2005, Theorem 1 (§3.3, pp. 1011–1012), eq. (24).**
Let `P = {𝐱 ∈ ℝⁿ | D𝐱 ⩾ 𝐝, 𝐱 ⩾ 𝟎} ≠ ∅` with rational `D`, `𝐝` (an addition: the page
names no field, and the theorem fails for irrational data), and `X = P ∩ ℤⁿ`. Then there
are finitely many integer points `𝐩_q ∈ X` (`q ∈ Q = Fin k`) and finitely many integer
rays `𝐩_r` of `P` (`r ∈ R = Fin l`) such that
`X = {𝐱 ∈ ℝⁿ₊ | 𝐱 = Σ_q 𝐩_q λ_q + Σ_r 𝐩_r λ_r, Σ_q λ_q = 1, λ ∈ ℤ₊^{|Q|+|R|}}`. -/
theorem discretization {m n : ℕ} (D : Matrix (Fin m) (Fin n) ℚ) (d : Fin m → ℚ)
    (hP : (polyhedronP D d).Nonempty) :
    ∃ (k l : ℕ) (p : Fin k → (Fin n → ℤ)) (w : Fin l → (Fin n → ℤ)),
      (∀ q, castVec (p q) ∈ integerPoints D d) ∧
      (∀ r, IsIntegerRay D (w r)) ∧
      integerPoints D d =
        {x : Fin n → ℝ | (∀ j, 0 ≤ x j) ∧
          ∃ (lamQ : Fin k → ℕ) (lamR : Fin l → ℕ),
            ∑ q, lamQ q = 1 ∧
            x = ∑ q, (lamQ q : ℝ) • castVec (p q) + ∑ r, (lamR r : ℝ) • castVec (w r)} := by sorry

end Lubbecke2005.Discretization

