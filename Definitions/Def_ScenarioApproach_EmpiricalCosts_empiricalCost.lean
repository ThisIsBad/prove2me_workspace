import Mathlib

namespace ScenarioApproach.EmpiricalCosts

/-- The `k`-th largest entry (`k` 1-based) of a finite list of reals `c 0, …, c (m-1)`:
`kthLargest c 1 ≥ kthLargest c 2 ≥ ⋯ ≥ kthLargest c m`. `Tuple.sort c` sorts `c` increasingly,
so the `k`-th largest entry sits at position `m - k` of the sorted list. Outside `1 ≤ k ≤ m` the
value is the junk `0`. -/
noncomputable def kthLargest {m : ℕ} (c : Fin m → ℝ) (k : ℕ) : ℝ :=
  if h : 1 ≤ k ∧ k ≤ m then c (Tuple.sort c ⟨m - k, by omega⟩) else 0

/-- Definition 8.1 (empirical costs). The cost values `ℓ(ν, δᵢ)`, `i = 1, …, m`, achieved by the
decision `ν` on the scenarios `δᵢ = ω (i-1)`, sorted in decreasing order: `empiricalCost ℓ ω ν k`
is `ℓ*_k`, the `k`-th largest of them (`1 ≤ k ≤ m`). The book takes `ν = ν*`. -/
noncomputable def empiricalCost {n m : ℕ} {Δ : Type*} (ℓ : EuclideanSpace ℝ (Fin n) → Δ → ℝ)
    (ω : Fin m → Δ) (ν : EuclideanSpace ℝ (Fin n)) (k : ℕ) : ℝ :=
  kthLargest (fun i => ℓ ν (ω i)) k

end ScenarioApproach.EmpiricalCosts
