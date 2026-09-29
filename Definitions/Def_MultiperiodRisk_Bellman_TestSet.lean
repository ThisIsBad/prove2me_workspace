import Mathlib

namespace MultiperiodRisk.Bellman

open MeasureTheory Filter Topology

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- A stopping time of the filtration `ℱ` taking values in `{0, …, N}`. -/
def IsBddStoppingTime (ℱ : Filtration ℕ m) (N : ℕ) (τ : Ω → WithTop ℕ) : Prop :=
  IsStoppingTime ℱ τ ∧ ∀ ω, τ ω ≤ (N : WithTop ℕ)

/-- A value process on the times `0, …, N`: adapted to `ℱ` and essentially bounded
under the reference probability `P₀`. Values at times `n > N` are never read. -/
def IsValueProcess (P₀ : Measure Ω) (ℱ : Filtration ℕ m) (N : ℕ) (X : ℕ → Ω → ℝ) : Prop :=
  (∀ n ≤ N, StronglyMeasurable[ℱ n] (X n)) ∧
    ∃ C : ℝ, ∀ n ≤ N, ∀ᵐ ω ∂P₀, |X n ω| ≤ C

/-- A closed convex set of test probabilities on `(Ω, ℱ_N)`, absolutely continuous with
respect to `P₀`, represented by the set of their densities `dℚ/dP₀`. -/
structure TestSet (P₀ : Measure Ω) (ℱ : Filtration ℕ m) (N : ℕ) where
  /-- The densities `dℚ/dP₀` of the test probabilities. -/
  set : Set (Ω → ℝ)
  stronglyMeasurable : ∀ f ∈ set, StronglyMeasurable[ℱ N] f
  nonneg : ∀ f ∈ set, 0 ≤ᵐ[P₀] f
  integrable : ∀ f ∈ set, Integrable f P₀
  integral_eq_one : ∀ f ∈ set, ∫ ω, f ω ∂P₀ = 1
  convex : Convex ℝ set
  /-- Closed in `L¹(Ω, ℱ_N, P₀)`. -/
  closed : ∀ (g : ℕ → Ω → ℝ) (f : Ω → ℝ), (∀ k, g k ∈ set) → StronglyMeasurable[ℱ N] f →
    Tendsto (fun k => eLpNorm (g k - f) 1 P₀) atTop (𝓝 0) → f ∈ set
  /-- Membership depends only on the `P₀`-a.e. class of the density. -/
  ae_saturated : ∀ f ∈ set, ∀ g : Ω → ℝ, StronglyMeasurable[ℱ N] g → g =ᵐ[P₀] f → g ∈ set

/-- The test probability `ℚ` with density `f` with respect to `P₀`. -/
noncomputable def Q (P₀ : Measure Ω) (f : Ω → ℝ) : Measure Ω :=
  P₀.withDensity (fun ω => ENNReal.ofReal (f ω))

/-- `𝒫ᵉ`: the densities of the test probabilities equivalent to `P₀` on `ℱ_N`. -/
def Pe {P₀ : Measure Ω} {ℱ : Filtration ℕ m} {N : ℕ} (D : TestSet P₀ ℱ N) : Set (Ω → ℝ) :=
  {f | f ∈ D.set ∧ ∀ᵐ ω ∂P₀, 0 < f ω}

/-- The density martingale `Z^ℚ_n = 𝐄_{P₀}[dℚ/dP₀ | ℱ_n]`. -/
noncomputable def Z (P₀ : Measure Ω) (ℱ : Filtration ℕ m) (f : Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  P₀[f | ℱ n]

/-- The terminal density of the result of pasting `ℚ⁰` (density `f₀`) and `ℚ` (density `f`)
at the stopping time `τ`: `L_N = Z⁰_τ · Z_N / Z_τ`, with `Z_N = f`. -/
noncomputable def pasteDensity (P₀ : Measure Ω) (ℱ : Filtration ℕ m) (f₀ f : Ω → ℝ)
    (τ : Ω → WithTop ℕ) : Ω → ℝ :=
  fun ω => stoppedValue (Z P₀ ℱ f₀) τ ω * f ω / stoppedValue (Z P₀ ℱ f) τ ω

/-- Definition 3.1: the set of test probabilities is stable under pasting. -/
def IsStable {P₀ : Measure Ω} {ℱ : Filtration ℕ m} {N : ℕ} (D : TestSet P₀ ℱ N) : Prop :=
  ∀ f₀ ∈ Pe D, ∀ f ∈ Pe D, ∀ τ : Ω → WithTop ℕ, IsBddStoppingTime ℱ N τ →
    pasteDensity P₀ ℱ f₀ f τ ∈ D.set

end MultiperiodRisk.Bellman
