import Mathlib
import Definitions.Def_KendallBD_MinVar_Setting

namespace KendallBD.MinVar

/-- The two interval identities behind Kendall's variance decomposition,
§6, display after "Then one can write", p. 12. -/
theorem fluct_integral_split (lam mu : ℝ → ℝ)
    (hadm : Admissible lam mu) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ τ in a..b, Real.exp (KendallBD.Sol.rho lam mu τ) * (lam τ + mu τ)) =
        (Real.exp (KendallBD.Sol.rho lam mu b) - Real.exp (KendallBD.Sol.rho lam mu a)) +
          2 * ∫ τ in a..b, Real.exp (KendallBD.Sol.rho lam mu τ) * lam τ ∧
    (∫ τ in a..b, Real.exp (KendallBD.Sol.rho lam mu τ) * (lam τ + mu τ)) =
        -(Real.exp (KendallBD.Sol.rho lam mu b) - Real.exp (KendallBD.Sol.rho lam mu a)) +
          2 * ∫ τ in a..b, Real.exp (KendallBD.Sol.rho lam mu τ) * mu τ := by sorry

end KendallBD.MinVar

