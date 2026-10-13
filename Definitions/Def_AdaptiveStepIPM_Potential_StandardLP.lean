import Mathlib

/-!
Mizuno, Todd, Ye, *On adaptive-step primal-dual interior-point algorithms for linear
programming*, Cornell ORIE Technical Report No. 944 (1990, rev. 1991), §1, p. 1.

The standard-form primal problem (P) minimizes `cᵀx` subject to `Ax = b`, `x ≥ 0`;
its dual (D) maximizes `bᵀy` subject to `Aᵀy + s = c`, `s ≥ 0`. The paper's `F⁰`
consists of pairs `(x, s)` for which `x` and `s` are strictly positive and some `y`
makes the two equalities hold. Dual variables `y` have no sign restriction.
-/

open Matrix

namespace AdaptiveStepIPM.Potential

/-- The data `(A, b, c)` of the standard-form primal–dual LP pair (P), (D), p. 1. -/
structure StandardLP (m n : ℕ) where
  A : Matrix (Fin m) (Fin n) ℝ
  b : Fin m → ℝ
  c : Fin n → ℝ

/-- Feasibility for the standard-form primal problem (P), p. 1. -/
def StandardLP.PrimalFeasible {m n : ℕ} (L : StandardLP m n) (x : Fin n → ℝ) : Prop :=
  L.A *ᵥ x = L.b ∧ ∀ j, 0 ≤ x j

/-- Feasibility for the dual problem (D), p. 1. The multiplier `y` is free. -/
def StandardLP.DualFeasible {m n : ℕ} (L : StandardLP m n)
    (y : Fin m → ℝ) (s : Fin n → ℝ) : Prop :=
  L.Aᵀ *ᵥ y + s = L.c ∧ ∀ j, 0 ≤ s j

/-- The strictly feasible set `F⁰` (p. 1): `x > 0`, `s > 0`, `Ax = b`, and `Aᵀy + s = c`
for some `y ∈ ℝᵐ`. -/
def StandardLP.StrictlyFeasible {m n : ℕ} (L : StandardLP m n)
    (x s : Fin n → ℝ) : Prop :=
  (∀ j, 0 < x j) ∧ (∀ j, 0 < s j) ∧ L.A *ᵥ x = L.b ∧
    ∃ y : Fin m → ℝ, L.Aᵀ *ᵥ y + s = L.c

end AdaptiveStepIPM.Potential
