import Mathlib

namespace JewellMRP.InfiniteStep

open Matrix

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Assumption 2 (p. 951): the embedded chain of the fixed stationary policy is ergodic, i.e.
`P` is a row-stochastic matrix (nonnegative entries, every row sums to one) that is
irreducible. Periodic chains are allowed. -/
def IsErgodic (P : Matrix S S ℝ) : Prop :=
  P ∈ Matrix.rowStochastic ℝ S ∧ P.IsIrreducible

/-- `π` is a stationary probability vector of `P`: nonnegative, summing to one, and `π P = π`. -/
def IsStationary (P : Matrix S S ℝ) (π : S → ℝ) : Prop :=
  (∀ i, 0 ≤ π i) ∧ ∑ i, π i = 1 ∧ π ᵥ* P = π

/-- The matrix `Π` every row of which is the row vector `π`: `Π i j = π j`. -/
def limitMatrix (π : S → ℝ) : Matrix S S ℝ :=
  Matrix.of fun _ j => π j

/-- The system gain `G = ∑ i, π i * ρ i` (A 6). -/
def gain (π ρ : S → ℝ) : ℝ :=
  ∑ i, π i * ρ i

/-- The fundamental matrix `Z = (I - P + Π)⁻¹` (A 7). (Mathlib's `⁻¹` returns `0` on a singular
matrix; every statement using `Z` comes with, or is preceded by, the invertibility of
`I - P + Π`.) -/
noncomputable def fundamentalMatrix (P : Matrix S S ℝ) (π : S → ℝ) : Matrix S S ℝ :=
  (1 - P + limitMatrix π)⁻¹

/-- The `n`-step expected return (I 16) under a fixed stationary policy:
`V(0)` is the terminal reward vector and `V(n) = ρ + P V(n-1)` for `n ≥ 1`. -/
def stepReturn (P : Matrix S S ℝ) (ρ V0 : S → ℝ) : ℕ → S → ℝ
  | 0 => V0
  | n + 1 => ρ + P *ᵥ stepReturn P ρ V0 n

/-- The bias vector after `n` steps, `W_i(n) = V_i(n) - G n`, with `G = gain π ρ`. -/
def biasSeq (P : Matrix S S ℝ) (π ρ V0 : S → ℝ) (n : ℕ) : S → ℝ :=
  stepReturn P ρ V0 n - fun _ => gain π ρ * (n : ℝ)

/-- The Cesàro mean `(1/n) ∑_{m=1}^{n} f(m)` of a sequence `f` in a real vector space
(it equals `0` at `n = 0`). -/
noncomputable def cesaroMean {E : Type*} [AddCommGroup E] [Module ℝ E] (f : ℕ → E) (n : ℕ) : E :=
  (n : ℝ)⁻¹ • ∑ m ∈ Finset.Icc 1 n, f m

end JewellMRP.InfiniteStep
