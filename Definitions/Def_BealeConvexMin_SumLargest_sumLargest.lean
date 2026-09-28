import Mathlib

namespace BealeConvexMin.SumLargest

/-- Beale (1955), §4, p. 177: "the sum of the `t` largest" of a finite family of reals.

For `v : Fin k → ℝ` and `τ ≤ k`, `sumLargest τ v` is the maximum, over all `τ`-element subsets
`S ⊆ {0, …, k-1}`, of `Σ_{i ∈ S} v i`. With ties this is still the sum of the `τ` largest values
counted with multiplicity. For `τ = 0` it is `0` (the empty sum).

For `τ > k` there is no `τ`-element subset and the value is the junk `0`; no statement of this
mission uses that case. -/
noncomputable def sumLargest {k : ℕ} (τ : ℕ) (v : Fin k → ℝ) : ℝ :=
  if h : τ ≤ k then
    (Finset.univ.powersetCard τ).sup'
      (Finset.powersetCard_nonempty.mpr (by simpa using h))
      (fun S => ∑ i ∈ S, v i)
  else 0

end BealeConvexMin.SumLargest
