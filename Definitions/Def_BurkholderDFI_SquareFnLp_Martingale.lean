import Mathlib

namespace BurkholderDFI.SquareFnLp

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

variable {Ω : Type*}

/-- §1, p. 20: the difference sequence `d_k = f_k − f_{k−1}` of `f = (f_1, f_2, …)`, with the
paper's convention `f_0 = 0` (so `d_1 = f_1`). The index `0` is padding: `dseq f 0 = 0`. -/
def dseq (f : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  if k = 0 then 0 else if k = 1 then f 1 ω else f k ω - f (k - 1) ω

/-- §1, p. 20: `S_n(f) = [Σ_{k=1}^n d_k²]^{1/2}`; `S_0(f) = 0`. -/
noncomputable def sqFnN (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.sqrt (∑ k ∈ Finset.Icc 1 n, dseq f k ω ^ 2))

/-- §1, p. 20: the square function `S(f) = S_∞(f) = [Σ_{k=1}^∞ d_k²]^{1/2}`, valued in `[0, ∞]`. -/
noncomputable def sqFn (f : ℕ → Ω → ℝ) (ω : Ω) : ℝ≥0∞ := ⨆ n : ℕ, sqFnN f n ω

/-- §1, p. 20: `f_n^* = sup_{1 ≤ k ≤ n} |f_k|`; `f_0^* = 0`. -/
noncomputable def maxFnN (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ⨆ k ∈ Finset.Icc 1 n, ENNReal.ofReal |f k ω|

/-- §1, p. 20: the maximal function `f^* = sup_n |f_n|`, valued in `[0, ∞]`. Applied to `dseq f`
it is `d^* = sup_k |d_k|`, and `maxFnN (dseq f) k` is `d_k^*` (§14, p. 33). -/
noncomputable def maxFn (f : ℕ → Ω → ℝ) (ω : Ω) : ℝ≥0∞ := ⨆ n : ℕ, maxFnN f n ω

/-- `‖Y‖_p = (E Y^p)^{1/p}` for a `[0, ∞]`-valued `Y` and a real exponent `p > 0`. -/
noncomputable def lpNormE [MeasurableSpace Ω] (P : Measure Ω) (p : ℝ) (Y : Ω → ℝ≥0∞) : ℝ≥0∞ :=
  (∫⁻ ω, Y ω ^ p ∂P) ^ (1 / p)

/-- §1, p. 20: `‖f‖_p = sup_{n ≥ 1} ‖f_n‖_p`; `f` is `L^p`-bounded iff this is finite. -/
noncomputable def pNorm [MeasurableSpace Ω] (P : Measure Ω) (p : ℝ) (f : ℕ → Ω → ℝ) : ℝ≥0∞ :=
  ⨆ n ∈ Set.Ici (1 : ℕ), lpNormE P p (fun ω => ENNReal.ofReal |f n ω|)

/-- Lemma 2.1 and (18.1): `μ = inf {n ≥ 1 : |f_n| > λ}`, with `inf ∅ = ∞` (`⊤ : ℕ∞`). -/
noncomputable def exitTime (f : ℕ → Ω → ℝ) (l : ℝ) (ω : Ω) : ℕ∞ :=
  ⨅ (n : ℕ) (_ : 1 ≤ n ∧ l < |f n ω|), (n : ℕ∞)

/-- `f_m` for `m ∈ {0, 1, …, ∞}`: `f_0 = 0` (§1) and `f_∞ = fInf`, the almost-everywhere limit,
which every statement using `valAt` supplies together with its convergence hypothesis. -/
noncomputable def valAt (f : ℕ → Ω → ℝ) (fInf : Ω → ℝ) (m : ℕ∞) (ω : Ω) : ℝ :=
  if m = ⊤ then fInf ω else if m.toNat = 0 then 0 else f m.toNat ω

/-- `S_m(f)` for `m ∈ {0, 1, …, ∞}`, with `S_∞(f) = S(f)` (§1). -/
noncomputable def sqFnAt (f : ℕ → Ω → ℝ) (m : ℕ∞) (ω : Ω) : ℝ≥0∞ :=
  if m = ⊤ then sqFn f ω else sqFnN f m.toNat ω

/-- §20, p. 39: `s(f) = [Σ_{k=1}^∞ E(d_k² | 𝒜_{k−1})]^{1/2}`, `ℱ k = 𝒜_k`. The conditional
expectation of the nonnegative, possibly non-integrable `d_k²` is taken in `[0, ∞]` (`condLExp`). -/
noncomputable def condSqFn [mΩ : MeasurableSpace Ω] (ℱ : Filtration ℕ mΩ) (P : Measure Ω)
    (f : ℕ → Ω → ℝ) (ω : Ω) : ℝ≥0∞ :=
  (∑' k : ℕ, condLExp (ℱ k) P (fun x => ENNReal.ofReal (dseq f (k + 1) x ^ 2)) ω) ^ (1 / 2 : ℝ)

/-- §§6–7, pp. 25–26: `Φ` is non-decreasing and continuous on `[0, ∞]`, `Φ(0) = 0`, and satisfies
the growth condition (6.1) `Φ(2λ) ≤ cΦ(λ)` with constant `c`. -/
structure IsPhi (Φ : ℝ≥0∞ → ℝ≥0∞) (c : ℝ≥0) : Prop where
  mono : Monotone Φ
  cont : Continuous Φ
  zero : Φ 0 = 0
  growth : ∀ x : ℝ≥0∞, Φ (2 * x) ≤ c * Φ x

/-- §15, p. 33: `Φ` is convex on `[0, ∞)` (read through its real values, which are finite on finite
arguments when `IsPhi Φ c` holds). -/
def IsConvexPhi (Φ : ℝ≥0∞ → ℝ≥0∞) : Prop :=
  ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x : ℝ => (Φ (ENNReal.ofReal x)).toReal)

/-- §20, p. 38: `Φ` is concave on `[0, ∞)` (read as for `IsConvexPhi`). -/
def IsConcavePhi (Φ : ℝ≥0∞ → ℝ≥0∞) : Prop :=
  ConcaveOn ℝ (Set.Ici (0 : ℝ)) (fun x : ℝ => (Φ (ENNReal.ofReal x)).toReal)

end BurkholderDFI.SquareFnLp
