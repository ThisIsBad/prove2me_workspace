import Mathlib
import Definitions.Def_WhittleGittins_Retirement_BanditProcess

namespace WhittleGittins.Retirement

open MeasureTheory ProbabilityTheory

/-- Relation (16) (p. 147) with the base case: `F̂(x, 0, M) = M`, and `F̂` satisfies the dynamic
programming equation `F̂ = max(M, maxᵢ Lᵢ F̂)`, the inner maximum over the active projects (and
`F̂ = M` when no project is active). -/
theorem relation16_dp_equation {N : ℕ} {X : Fin N → Type*} [∀ i, MeasurableSpace (X i)]
    (B : BanditProcess N X) (x : ∀ j, X j) (M : ℝ) :
    Fhat B x 0 M = M ∧
      ∀ s : Fin N → ℕ, Fhat B x s M = bellmanMax s M (fun i => LFhat B i x s M) := by sorry

end WhittleGittins.Retirement

