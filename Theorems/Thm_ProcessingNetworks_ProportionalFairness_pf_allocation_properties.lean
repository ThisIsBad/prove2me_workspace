import Mathlib
import Definitions.Def_ProcessingNetworks_ProportionalFairness_PFOptimization

namespace ProcessingNetworks.ProportionalFairness

/-- Lemma 10.1, Dai & Harrison p. 184 (PDF p. 200): given `IsPFDomain AllocSet` and a demand
vector `z ≥ 0`, all six stated properties of the PF allocation function `ψ` hold. (a) existence is
built into `psi`'s definition; uniqueness and strict positivity hold on `I+(z) = {i : z_i > 0}`.
(b) extremality: if some class has positive demand, every feasible `x` is dominated by `ψ(z)` in
some such class. (c) scale invariance on `I+(z)`. (d) continuity of `ψ_i(·)` at `z`, for
`i ∈ I+(z)`. (e) `ψ(z)` strictly beats every interior point when `z ≠ 0`. (f) the optimal value
`f(·, ψ(·))` is continuous at `z`. -/
theorem pf_allocation_properties
    {I : ℕ} (AllocSet : Set (Fin I → ℝ)) (hdom : IsPFDomain AllocSet)
    (z : Fin I → ℝ) (hz : ∀ i, 0 ≤ z i) :
    IsPFMaximizer AllocSet z (psi AllocSet z) ∧
    (∀ i, 0 < z i →
      0 < psi AllocSet z i ∧ ∀ x, IsPFMaximizer AllocSet z x → x i = psi AllocSet z i) ∧
    ((∃ i, 0 < z i) → ∀ x ∈ AllocSet, ∃ i, 0 < z i ∧ x i ≤ psi AllocSet z i) ∧
    (∀ r : ℝ, 0 < r → ∀ i, 0 < z i → psi AllocSet (fun i => r * z i) i = psi AllocSet z i) ∧
    (∀ i, 0 < z i →
      ContinuousWithinAt (fun w => psi AllocSet w i) {w : Fin I → ℝ | ∀ i, 0 ≤ w i} z) ∧
    (z ≠ 0 → ∀ x ∈ interior AllocSet, f z x < f z (psi AllocSet z)) ∧
    ContinuousWithinAt (fun w => f w (psi AllocSet w)) {w : Fin I → ℝ | ∀ i, 0 ≤ w i} z := by sorry

end ProcessingNetworks.ProportionalFairness
