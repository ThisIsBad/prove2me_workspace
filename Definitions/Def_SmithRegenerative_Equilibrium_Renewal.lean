import Mathlib
import Definitions.Def_QueueingFundamentals_MG1_transforms

namespace SmithRegenerative.Equilibrium

open MeasureTheory QueueingFundamentals.MG1

/-- **Cycle law** (Smith 1955, §2·1, p. 9). `F` is the law of a renewal interval `tᵢ` (`i ≥ 1`):
a probability measure on `ℝ` concentrated on `[0, ∞)` ("non-negative") which is not the unit mass
at `0` ("not zero with probability one", i.e. `P{tᵢ = 0} < 1`).

Formalization Note: distributions are measures on `ℝ`; the paper's distribution function is
`F(t) = F (Set.Iic t)` and `1 − F(t) = F (Set.Ioi t)`. The renewal intervals are proper (finite
almost surely), as in §2·1 and Theorem A. -/
def IsCycleLaw (F : Measure ℝ) : Prop :=
  IsProbabilityMeasure F ∧ F (Set.Iio 0) = 0 ∧ F ≠ Measure.dirac 0

/-- **Delay law** (Smith 1955, §2·1 and §2·2, pp. 9–10). `K` is the law of the initial delay `t₀`:
a measure on `ℝ` concentrated on `[0, ∞)` with total mass `K(+∞) = K ℝ ≤ 1` (Theorem A allows an
improper delay, `K(+∞) < 1`). -/
def IsDelayLaw (K : Measure ℝ) : Prop :=
  K (Set.Iio 0) = 0 ∧ K Set.univ ≤ 1

/-- **Mean** `μ₁ = E tᵢ = ∫ x dF(x)` (Smith 1955, (2·1·1), p. 9), as an extended non-negative real:
`μ₁ = ∞` is a value, not a junk default.

Formalization Note: the integrand is `ENNReal.ofReal x`; for a law on `[0, ∞)` this is `∫ x dF`. -/
noncomputable def mean (F : Measure ℝ) : ENNReal :=
  ∫⁻ x, ENNReal.ofReal x ∂F

/-- **Renewal measure** `H_K` (Smith 1955, (2·1·4)–(2·1·5), p. 9): `F_K^{(0)} = K`,
`F_K^{(n)} = F_K^{(n−1)} ∗ F`, `H_K = Σ_{n ≥ 0} F_K^{(n)}`, as a measure on `ℝ`:
`H_K = Σ_{n ≥ 0} K ∗ F^{∗n}`, with `F^{∗0} = δ₀` (`convPow` of the referenced
`QueueingFundamentals.MG1.transforms`). The paper's renewal function is `H_K(t) = H_K (Set.Iic t)`,
and a Stieltjes integral `∫₀^t Ψ(t − t′) dH_K(t′)` is `∫ s in Set.Icc 0 t, Ψ (t - s) ∂H_K`
(closed at both ends, so atoms of `H_K` at `0` and at `t` are included). -/
noncomputable def renewalMeasure (K F : Measure ℝ) : Measure ℝ :=
  Measure.sum (fun n : ℕ => K.conv (convPow F n))

/-- **Aperiodicity** `ϖ = 0` (Smith 1955, §2·2, p. 10). The paper calls `F` *periodic* with period
`ϖ > 0` when `F` is a step function all of whose jumps lie on `{nϖ : n = 0, 1, 2, …}` (and `ϖ` is the
greatest such number), and sets `ϖ = 0` when `F` is not periodic. A step function with all jumps on
`{nϖ}` is exactly a law giving mass one to `{nϖ : n ∈ ℕ}`, so `ϖ = 0` holds iff no `ϖ > 0` has
`F {nϖ : n ∈ ℕ} = 1`. (For a cycle law `F ≠ δ₀` a greatest such `ϖ` exists whenever one exists.) -/
def IsAperiodic (F : Measure ℝ) : Prop :=
  ¬ ∃ ϖ : ℝ, 0 < ϖ ∧ F {x : ℝ | ∃ n : ℕ, x = (n : ℝ) * ϖ} = 1

/-- **The class 𝔖** (Smith 1955, §2·2, p. 10): "If for some k the k-th iterated convolution of F(t)
with itself possesses an absolutely continuous component we write F(t) ∈ 𝔖." The `k`-th iterated
convolution `F^{∗k}` (`k ≥ 1`) has a non-zero absolutely continuous part in its Lebesgue
decomposition with respect to Lebesgue measure iff it is not mutually singular with Lebesgue
measure. `k = 0` (the unit mass `δ₀`) is excluded. -/
def InClassS (F : Measure ℝ) : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ ¬ (convPow F k).MutuallySingular volume

end SmithRegenerative.Equilibrium
