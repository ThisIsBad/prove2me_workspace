import Mathlib

namespace GoldieRenewal.Kesten

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-! The partial products and partial sums of Proposition 4.2 (Goldie 1991, p. 136).

The sequence `(Q_k, M_k)`, `k = 1, 2, …`, of the paper is stored 0-based: `Q i`, `M i` for
`i = 0, 1, …` stand for the paper's `Q_{i+1}`, `M_{i+1}`. Empty products are `1`, empty sums `0`. -/

/-- `Π_j := M₁ ⋯ M_j` (paper, p. 136; also `Π_n` of §4, p. 135). With 0-based storage this is
`∏_{i < j} M i`; `Π₀ = 1`. -/
def piProd {Ω : Type*} (M : ℕ → Ω → ℝ) (j : ℕ) (ω : Ω) : ℝ :=
  ∏ i ∈ Finset.range j, M i ω

/-- `R_n := Σ_{k=1}^n Π_{k−1} Q_k` (paper, p. 136). With 0-based storage this is
`Σ_{i < n} Π_i Q i`; `R₀ = 0`. -/
def partialSum {Ω : Type*} (Q M : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range n, piProd M i ω * Q i ω

/-- `Π_{j,n} := Π_{k=j+1}^n M_k` (paper, p. 136). With 0-based storage this is
`∏_{j ≤ i < n} M i`; it is `1` when `n ≤ j`. -/
def piProdFrom {Ω : Type*} (M : ℕ → Ω → ℝ) (j n : ℕ) (ω : Ω) : ℝ :=
  ∏ i ∈ Finset.Ico j n, M i ω

/-- `R_{j,n} := Σ_{k=j+1}^n Π_{j,k−1} Q_k` (paper, p. 136). With 0-based storage this is
`Σ_{j ≤ i < n} Π_{j,i} Q i`; it is `0` when `n ≤ j`. -/
def partialSumFrom {Ω : Type*} (Q M : ℕ → Ω → ℝ) (j n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.Ico j n, piProdFrom M j i ω * Q i ω

/-- **Median** of a law (Goldie 1991, p. 136, "med denotes median"): `a` is a median of the law
`ν` on `ℝ` when `ν[a, ∞) ≥ 1/2` and `ν(−∞, a] ≥ 1/2`. Medians need not be unique. -/
def IsMedian (ν : Measure ℝ) (a : ℝ) : Prop :=
  (2 : ℝ≥0∞)⁻¹ ≤ ν (Set.Ici a) ∧ (2 : ℝ≥0∞)⁻¹ ≤ ν (Set.Iic a)

/-- **The paper's `‖X‖_p`** (Goldie 1991, §1, p. 127) for `X` with law `ν`:
`‖X‖_p := E|X|^p` if `0 < p ≤ 1`, and `(E|X|^p)^{1/p}` if `1 ≤ p < ∞` (the two agree at `p = 1`).

**Formalization Note** `E|X|^p` is the Bochner integral `∫ |x|^p dν`; every statement using this
quantity also asserts or assumes that `|x|^p` is `ν`-integrable, so the value is never a junk `0`. -/
noncomputable def goldieNorm (p : ℝ) (ν : Measure ℝ) : ℝ :=
  if p ≤ 1 then ∫ x, |x| ^ p ∂ν else (∫ x, |x| ^ p ∂ν) ^ (1 / p)

end GoldieRenewal.Kesten
