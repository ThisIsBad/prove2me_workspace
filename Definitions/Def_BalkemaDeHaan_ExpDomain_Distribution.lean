import Mathlib
import Definitions.Def_BalkemaDeHaan_LimitTypes_ResidualLife

namespace BalkemaDeHaan.ExpDomain

open Filter MeasureTheory ProbabilityTheory

/-- Weak convergence of real distribution functions, evaluated at each continuity point. -/
def WeakConvergenceReal (H : ℝ → ℝ → ℝ) (G : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, ContinuousAt G x → Tendsto (fun t : ℝ => H t x) atTop (nhds (G x))

/-- Weak convergence of sequential distribution functions. -/
def WeakConvergenceNat (H : ℕ → ℝ → ℝ) (G : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, ContinuousAt G x → Tendsto (fun n : ℕ => H n x) atTop (nhds (G x))

end BalkemaDeHaan.ExpDomain
