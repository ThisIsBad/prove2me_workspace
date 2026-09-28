import Mathlib
import Definitions.Def_HeldWolfeCrowder_CoreProblem_Setting

namespace HeldWolfeCrowder.CoreProblem

open scoped InnerProductSpace
open Filter Topology

/-- **Held, Wolfe & Crowder (1974), Eq. (2.10), p. 67.** Let `π*` be a maximizer of `w`
(`w(π*) = w* = max w`). If the index `k` attains the minimum (2.2) at `π` (so
`v_k ∈ V(π) ⊆ ∂w(π)`; in particular for `π = π^j`, `k = k(j)`), then
`w* − w(π) ≤ v_k · (π* − π)`. -/
theorem subgradient_inequality {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (c : ι → ℝ) (v : ι → EuclideanSpace ℝ (Fin n))
    (πstar : EuclideanSpace ℝ (Fin n)) (hstar : ∀ π', w c v π' ≤ w c v πstar)
    (π : EuclideanSpace ℝ (Fin n)) (k : ι) (hk : IsMinIndex c v π k) :
    w c v πstar - w c v π ≤ ⟪v k, πstar - π⟫_ℝ := by sorry

end HeldWolfeCrowder.CoreProblem
