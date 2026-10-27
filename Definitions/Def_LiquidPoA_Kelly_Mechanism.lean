import Mathlib

namespace LiquidPoA.Kelly

open Set Finset

/-- A nonnegative signal vector for the `n` players of Section 2. -/
def IsSignal {n : ℕ} (s : Fin n → ℝ) : Prop := ∀ i, 0 ≤ s i

/-- The simplex of unit allocations, together with the zero allocation. -/
def IsAllocation {n : ℕ} (d : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ d i) ∧ ((∑ i, d i = 1) ∨ ∀ i, d i = 0)

/-- An allocation and payment rule for a single divisible resource. -/
structure Mechanism (n : ℕ) where
  alloc : (Fin n → ℝ) → Fin n → ℝ
  pay : (Fin n → ℝ) → Fin n → ℝ

/-- Own-signal allocation with the other players' signals fixed. -/
def allocIn {n : ℕ} (M : Mechanism n) (s : Fin n → ℝ) (i : Fin n) : ℝ → ℝ :=
  fun y => M.alloc (Function.update s i y) i

/-- Own-signal payment with the other players' signals fixed. -/
def payIn {n : ℕ} (M : Mechanism n) (s : Fin n → ℝ) (i : Fin n) : ℝ → ℝ :=
  fun y => M.pay (Function.update s i y) i

/-- The signal vectors in `𝕏ₙ`, having two distinct positive coordinates. -/
def InX {n : ℕ} (s : Fin n → ℝ) : Prop :=
  IsSignal s ∧ ∃ i j, i ≠ j ∧ 0 < s i ∧ 0 < s j

/-- Section 2's mechanism properties (pp. 4–5) and the strict derivative condition of footnote 5
(p. 9). "Increasing" is strict: the paper says "monotone non-decreasing" when it means the weak
notion (p. 5, valuations). The only exception the page makes is the allocation `g_i(y, 0_{-i}) = 1`
(`alone`), so payments are strictly increasing in the own signal for every `s_{-i}`.
Differentiability fails only at the all-zero vector (`diff_alone` is on `Ioi 0`); the payment of a
sole deviator from the zero vector is continuous at `0` (`pay_cont_zero`), as p. 5 uses: "due to the
continuity of the payment function and the fact that it is equal to zero on input the signal vector 0". -/
structure IsRAMechanism {n : ℕ} (M : Mechanism n) : Prop where
  alloc_mem : ∀ s, IsSignal s → IsAllocation (M.alloc s)
  pay_nonneg : ∀ s, IsSignal s → ∀ i, 0 ≤ M.pay s i
  anon_alloc : ∀ (σ : Equiv.Perm (Fin n)) (s : Fin n → ℝ),
    IsSignal s → M.alloc (s ∘ σ) = M.alloc s ∘ σ
  anon_pay : ∀ (σ : Equiv.Perm (Fin n)) (s : Fin n → ℝ),
    IsSignal s → M.pay (s ∘ σ) = M.pay s ∘ σ
  zero_sig : ∀ s, IsSignal s → ∀ i, s i = 0 →
    M.alloc s i = 0 ∧ M.pay s i = 0
  alone : ∀ i (y : ℝ), 0 < y → M.alloc (Function.update 0 i y) i = 1
  alloc_incr : ∀ s, IsSignal s → ∀ i, (∃ j, j ≠ i ∧ 0 < s j) →
    StrictMonoOn (allocIn M s i) (Ici 0)
  pay_incr : ∀ s, IsSignal s → ∀ i,
    StrictMonoOn (payIn M s i) (Ici 0)
  pay_cont_zero : ∀ i, ContinuousWithinAt (payIn M 0 i) (Ici 0) 0
  diff : ∀ s, IsSignal s → ∀ i, (∃ j, j ≠ i ∧ 0 < s j) →
    DifferentiableOn ℝ (allocIn M s i) (Ici 0) ∧
    DifferentiableOn ℝ (payIn M s i) (Ici 0)
  diff_alone : ∀ s, IsSignal s → ∀ i, (∀ j, j ≠ i → s j = 0) →
    DifferentiableOn ℝ (allocIn M s i) (Ioi 0) ∧
    DifferentiableOn ℝ (payIn M s i) (Ioi 0)
  deriv_pos : ∀ s, InX s → ∀ i,
    0 < derivWithin (allocIn M s i) (Ici 0) (s i)

end LiquidPoA.Kelly
