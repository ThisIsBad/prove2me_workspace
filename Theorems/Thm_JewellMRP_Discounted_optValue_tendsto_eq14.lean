import Mathlib
import Definitions.Def_JewellMRP_Discounted_MRP
import Definitions.Def_JewellMRP_Discounted_PolicyIteration

open Filter Topology

namespace JewellMRP.Discounted

/-- Eq. (14), p. 945: for `α > 0` the optimal `n`-step returns `V_i(n, α)` of (6) converge,
as `n → ∞`, to a limit that does not depend on the boundary rewards and solves
`v_i = max_z [ρ^z_i(α) + Σ_j p^z_{ij} f̃^z_{ij}(α) v_j]`. -/
theorem optValue_tendsto_eq14 {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
    (M : MRP S A) {α : ℝ} (hα : 0 < α) :
    ∃ v : S → ℝ, (∀ i, v i = maxTest M α v i) ∧
      ∀ V0 : S → ℝ, Tendsto (optValue M α V0) atTop (𝓝 v) := by sorry

end JewellMRP.Discounted
