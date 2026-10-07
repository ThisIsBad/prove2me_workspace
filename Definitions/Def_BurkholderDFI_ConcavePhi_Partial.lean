import Mathlib

namespace BurkholderDFI.ConcavePhi

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

variable {Ω : Type*}

/-- §20, proof of Theorem 20.1, p. 38: the partial sums `Z_n = Σ_{k=1}^n z_k`, `0 ≤ n ≤ ∞`, of a
sequence `z_1, z_2, …` of `[0, ∞]`-valued functions (`z k` is `z_k`; the index `0` is unused).
For `n = ⊤` this is `Z = Z_∞ = Σ_{k=1}^∞ z_k`; `Z_0 = 0`. -/
noncomputable def Zpart (z : ℕ → Ω → ℝ≥0∞) (n : ℕ∞) (ω : Ω) : ℝ≥0∞ :=
  ∑' k : ℕ, if (((k + 1 : ℕ) : ℕ∞) ≤ n) then z (k + 1) ω else 0

/-- §20, proof of Theorem 20.1, p. 38: `W_n = Σ_{k=1}^n E(z_k | 𝒜_{k−1})`, `0 ≤ n ≤ ∞`, where
`ℱ k = 𝒜_k` and the conditional expectation of the nonnegative, possibly non-integrable `z_k` is
taken in `[0, ∞]` (`condLExp`). For `n = ⊤` this is `W = W_∞`; `W_0 = 0`. -/
noncomputable def Wpart [mΩ : MeasurableSpace Ω] (ℱ : Filtration ℕ mΩ) (P : Measure Ω)
    (z : ℕ → Ω → ℝ≥0∞) (n : ℕ∞) (ω : Ω) : ℝ≥0∞ :=
  ∑' k : ℕ, if (((k + 1 : ℕ) : ℕ∞) ≤ n) then condLExp (ℱ k) P (z (k + 1)) ω else 0

/-- §20, proof of Theorem 20.1, p. 38: `τ = inf {n ≥ 0 : W_{n+1} > λ}`, with `inf ∅ = ∞`
(`⊤ : ℕ∞`). -/
noncomputable def stopIdx [mΩ : MeasurableSpace Ω] (ℱ : Filtration ℕ mΩ) (P : Measure Ω)
    (z : ℕ → Ω → ℝ≥0∞) (l : ℝ≥0) (ω : Ω) : ℕ∞ :=
  ⨅ (n : ℕ) (_ : (l : ℝ≥0∞) < Wpart ℱ P z ((n + 1 : ℕ) : ℕ∞) ω), (n : ℕ∞)

end BurkholderDFI.ConcavePhi
