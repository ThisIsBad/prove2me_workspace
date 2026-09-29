import Mathlib
import Definitions.Def_PolyhedralSOC_UpperBound_System8

namespace PolyhedralSOC.UpperBound

/-- Ben-Tal & Nemirovski, *On Polyhedral Approximations of the Second-Order Cone*,
Math. Oper. Res. 26(2):193–205 (2001), Proposition 2.1, part (i), p. 199 (PDF p. 7;
proof p. 200): for every positive integer `ν`, if `(x₁, x₂, x₃) ∈ L²`, i.e.
`√(x₁² + x₂²) ≤ x₃`, then `(x₁, x₂, x₃)` can be extended to a solution of (8). -/
theorem planar_approx_extend (ν : ℕ) (hν : 1 ≤ ν) (x₁ x₂ x₃ : ℝ)
    (hx : Real.sqrt (x₁ ^ 2 + x₂ ^ 2) ≤ x₃) :
    ∃ ξ η : ℕ → ℝ, System8 ν x₁ x₂ x₃ ξ η := by sorry

end PolyhedralSOC.UpperBound
