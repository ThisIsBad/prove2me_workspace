import Mathlib

namespace ScenarioApproach.Fast

/-- The `N₂` rule of FAST (p. 95): for `ε, β ∈ (0, 1)`, if `N₂ ≥ (1/ε) ln(1/β)` then the
right-hand side of (8.5) is at most `β`, whatever `N₁` and `d`:
`(1-ε)^{N₂} ∑_{i=0}^{d-1} (N₁ choose i) ε^i (1-ε)^{N₁-i} ≤ β`. -/
theorem fast_bound_le_of_N2 (d N₁ N₂ : ℕ) (ε β : ℝ)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hN₂ : (1 / ε) * Real.log (1 / β) ≤ N₂) :
    (1 - ε) ^ N₂ *
        ∑ i ∈ Finset.range d, (N₁.choose i : ℝ) * ε ^ i * (1 - ε) ^ (N₁ - i) ≤ β := by sorry

end ScenarioApproach.Fast

