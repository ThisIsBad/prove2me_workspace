import Mathlib
import Definitions.Def_ShockWear_CumDamage_Model

namespace ShockWear.Inherit

open scoped ENNReal

/-- The chance of failure at shock `k`, including failure at time zero. -/
def failProb (P : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1 - P 0
  | k + 1 => P k - P (k + 1)

/-- The positive-time density in (2.3), with its sum reindexed from zero. -/
noncomputable def shockDens (lam : ℝ) (P : ℕ → ℝ) (t : ℝ) : ℝ :=
  lam * ∑' k, failProb P (k + 1) * ShockWear.CumDamage.poisW lam t k

/-- The weakly decreasing successive-ratio condition for a PF₂ sequence,
expressed without division at zero. -/
def IsPF2SeqFrom (m : ℕ) (a : ℕ → ℝ) : Prop :=
  ∀ j k, m ≤ j → j ≤ k → a (k + 1) * a j ≤ a (j + 1) * a k

/-- The positive-time PF₂ density condition of p. 631. -/
def IsPF2Dens (f : ℝ → ℝ) : Prop :=
  ∀ x, 0 < x → ∀ s t, 0 < s → s ≤ t → f (x + t) * f s ≤ f (x + s) * f t

/-- Increasing hazard rate, stated through decreasing survival ratios on the
life-distribution domain `t ≥ 0`. -/
def IsIHR (Fb : ℝ → ℝ) : Prop :=
  ∀ x, 0 < x → ∀ s t, 0 ≤ s → s ≤ t → Fb (x + t) * Fb s ≤ Fb (x + s) * Fb t

/-- On a set, a sign pattern cannot return to positive after passing from
positive to negative. This expresses at most two sign changes in the order
negative, positive, negative. -/
def SignMPM (g : ℝ → ℝ) (D : Set ℝ) : Prop :=
  ∀ r ∈ D, ∀ s ∈ D, ∀ t ∈ D, r < s → s < t → ¬ (0 < g r ∧ g s < 0 ∧ 0 < g t)

/-- Decreasing hazard rate (ii′), p. 632, stated through increasing survival ratios
on the life-distribution domain `t ≥ 0`. -/
def IsDHR (Fb : ℝ → ℝ) : Prop :=
  ∀ x, 0 < x → ∀ s t, 0 ≤ s → s ≤ t → Fb (x + s) * Fb t ≤ Fb (x + t) * Fb s

/-- `∫₀^∞ F̄(x + t) dx`, valued in `[0, ∞]`. -/
noncomputable def resInt (Fb : ℝ → ℝ) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in Set.Ioi 0, ENNReal.ofReal (Fb (x + t))

/-- (iii) Decreasing mean residual life: `∫₀^∞ F̄(x + t) dx / F̄(t)` is decreasing
for `t ≥ 0` wherever `F̄(t) > 0`, computed in `[0, ∞]`. -/
def IsDMRL (Fb : ℝ → ℝ) : Prop :=
  AntitoneOn (fun t => resInt Fb t / ENNReal.ofReal (Fb t)) {t | 0 ≤ t ∧ 0 < Fb t}

/-- (vi) New better than used in expectation:
`∫₀^∞ F̄ ≥ ∫₀^∞ F̄(t + x) dx / F̄(t)` for all `t ≥ 0` with `F̄(t) > 0`, in `[0, ∞]`. -/
def IsNBUE (Fb : ℝ → ℝ) : Prop :=
  ∀ t, 0 ≤ t → 0 < Fb t → resInt Fb t / ENNReal.ofReal (Fb t) ≤ resInt Fb 0

/-- (i′) Logarithmically convex density on `(0, ∞)`: `f(x + t)/f(t)` is increasing
in `t > 0` whenever `x > 0` (cross-multiplied). -/
def IsLogConvexDens (f : ℝ → ℝ) : Prop :=
  ∀ x, 0 < x → ∀ s t, 0 < s → s ≤ t → f (x + s) * f t ≤ f (x + t) * f s

end ShockWear.Inherit
