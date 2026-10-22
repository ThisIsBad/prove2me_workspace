import Mathlib
import Definitions.Def_FracPackCover_Covering_Basic
import Definitions.Def_FracPackCover_Covering_ImproveCover
import Definitions.Def_FracPackCover_Covering_Driver

namespace FracPackCover.Covering

/-- Theorem 3.7 (Plotkin–Shmoys–Tardos, Cornell ORIE TR 999, p. 21), with the explicit constants
of its proof. For `0 < ε₀ < 1`, every covering instance (`A ≥ 0`, `b > 0`, `P` convex, nonempty, in
the nonnegative orthant), every width bound `ρ` and every exact maximization oracle, the covering
algorithm of §3 (`coverAlgorithm`: initial solution, phase `ε = 1/6`, `ε`-scaling) stops, using at most
`N = m + (⌈log₂ m⌉ + 1)(2 + 4320 ρ ln(24m)) + 2⌈log₂(1/ε₀)⌉ + 9408 ρ ε₀⁻² ln(24m/ε₀)` calls to
subroutine (7) (the paper writes `O(m + ρ log² m + ε⁻² ρ log(m ε⁻¹))`), and either returns `x ∈ P`
with `A x ≥ (1 − ε₀) b` or reports that no `x ∈ P` has `A x ≥ b`, correctly. -/
theorem theorem_3_7 {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (P : Set (Fin n → ℝ)) (hdata : IsCoveringData A b P) (ρ : ℝ) (hρ : WidthBound A b P ρ)
    (orc : (Fin m → ℝ) → (Fin n → ℝ)) (horc : IsMaxOracle A P orc)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ < 1) :
    let N : ℝ := (m : ℝ) + ((⌈Real.logb 2 m⌉₊ : ℝ) + 1) * (2 + 4320 * ρ * Real.log (24 * m)) +
      2 * (⌈Real.logb 2 ε₀⁻¹⌉₊ : ℝ) + 9408 * ρ * ε₀⁻¹ ^ 2 * Real.log (24 * m * ε₀⁻¹)
    ∃ out : CoverOutcome n, ∃ c : ℕ,
      coverAlgorithm A b orc ρ ε₀ ⌈N⌉₊ = some (out, c) ∧ (c : ℝ) ≤ N ∧
      (∀ x, out = .approx x → x ∈ P ∧ ∀ i, (1 - ε₀) * b i ≤ rowVal A x i) ∧
      (out = .infeasible → ¬ ∃ x' ∈ P, ∀ i, b i ≤ rowVal A x' i) := by sorry

end FracPackCover.Covering

