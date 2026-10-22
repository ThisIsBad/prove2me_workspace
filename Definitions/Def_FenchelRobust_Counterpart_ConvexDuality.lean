import Mathlib

namespace FenchelRobust.Counterpart

/-- The support function of a subset of a finite-dimensional real vector space, (3). -/
noncomputable def supportFun {k : ℕ} (S : Set (Fin k → ℝ)) (y : Fin k → ℝ) : EReal :=
  ⨆ a ∈ S, ((y ⬝ᵥ a : ℝ) : EReal)

/-- The convex conjugate of a real function restricted to its effective domain. -/
noncomputable def convexConj {k : ℕ} (C : Set (Fin k → ℝ))
    (F : (Fin k → ℝ) → ℝ) (y : Fin k → ℝ) : EReal :=
  ⨆ a ∈ C, ((y ⬝ᵥ a - F a : ℝ) : EReal)

/-- The lower (concave) conjugate of a real function on its effective domain, (1). -/
noncomputable def concaveConj {k : ℕ} (D : Set (Fin k → ℝ))
    (G : (Fin k → ℝ) → ℝ) (y : Fin k → ℝ) : EReal :=
  ⨅ a ∈ D, ((a ⬝ᵥ y - G a : ℝ) : EReal)

end FenchelRobust.Counterpart
