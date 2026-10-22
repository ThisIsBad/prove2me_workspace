import Mathlib
import Definitions.Def_FracPackCover_Covering_Basic
import Definitions.Def_FracPackCover_Covering_ImproveCover

namespace FracPackCover.Covering

/-- Theorem 3.5 (Plotkin–Shmoys–Tardos, Cornell ORIE TR 999, p. 20), with the explicit constants
of its proof. Let `0 < ε < 1`, `x ∈ P` with `λ(x) > 0`, `ρ` a width bound and `orc` an exact
maximization oracle.
1. IMPROVE-COVER(x, ε) stops within `B₁ = 2 + 20 ρ ε⁻³ ln(4 m ε⁻¹)` evaluations of its while-test
   and makes at most `B₁` oracle calls (the paper writes `O(ε⁻³ ρ log(m ε⁻¹))` iterations).
2. If moreover `ε ≤ 1/12` and `x` is `6ε`-optimal (`(1 − 6ε) λ(x') ≤ λ(x)` for every `x' ∈ P`), it
   stops within `B₂ = 2 + 196 ρ ε⁻² ln(4 m ε⁻¹)` tests and makes at most `B₂` oracle calls (the paper
   writes `O(ε⁻² ρ log(m ε⁻¹))`; its second sentence names IMPROVE-PACKING, a misprint for
   IMPROVE-COVER). -/
theorem theorem_3_5 {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (P : Set (Fin n → ℝ)) (hdata : IsCoveringData A b P) (ρ : ℝ) (hρ : WidthBound A b P ρ)
    (orc : (Fin m → ℝ) → (Fin n → ℝ)) (horc : IsMaxOracle A P orc)
    (x : Fin n → ℝ) (hx : x ∈ P) (hlam : 0 < lam A b x) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    (∃ x' : Fin n → ℝ, ∃ c : ℕ,
      improveCover A b orc ρ ε x ⌈2 + 20 * ρ * ε⁻¹ ^ 3 * Real.log (4 * m * ε⁻¹)⌉₊ = some (x', c) ∧
      (c : ℝ) ≤ 2 + 20 * ρ * ε⁻¹ ^ 3 * Real.log (4 * m * ε⁻¹)) ∧
    (ε ≤ 1 / 12 → (∀ x' ∈ P, (1 - 6 * ε) * lam A b x' ≤ lam A b x) →
      ∃ x' : Fin n → ℝ, ∃ c : ℕ,
        improveCover A b orc ρ ε x ⌈2 + 196 * ρ * ε⁻¹ ^ 2 * Real.log (4 * m * ε⁻¹)⌉₊ =
          some (x', c) ∧
        (c : ℝ) ≤ 2 + 196 * ρ * ε⁻¹ ^ 2 * Real.log (4 * m * ε⁻¹)) := by sorry

end FracPackCover.Covering

