import Mathlib
import Definitions.Def_HunterPDE_Shared_PartialDeriv

open MeasureTheory
open scoped ContDiff

namespace HunterPDE.Shared

/-- `φ ∈ C_c^∞(Ω)`: `φ : ℝⁿ → ℝ` is infinitely differentiable (`∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)`,
i.e. `C^∞`, not analytic), has compact support, and its (closed) support lies in `Ω`. -/
def IsTestFunction {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ω

/-- Definition 3.2 (and 3.1 for `|α| = 1`) of Hunter, *Notes on PDEs*: `g` is a weak derivative
`∂^α f` of `f` on the open set `Ω`. Both `f` and `g` are locally integrable on `Ω`, and
`∫_Ω g φ dx = (-1)^{|α|} ∫_Ω f ∂^α φ dx` for every `φ ∈ C_c^∞(Ω)`. Real-valued functions,
multi-index `α : Fin n → ℕ` with `|α| = ∑ i, α i`, coordinates 0-based. Only the values of `f`
and `g` on `Ω` matter. -/
def HasWeakDeriv {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (α : Fin n → ℕ)
    (f g : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  LocallyIntegrableOn f Ω volume ∧ LocallyIntegrableOn g Ω volume ∧
    ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ, IsTestFunction Ω φ →
      ∫ x in Ω, g x * φ x = (-1 : ℝ) ^ (∑ i, α i) * ∫ x in Ω, f x * multiDeriv φ α x

open Classical in
/-- The weak derivative `∂^α f` on `Ω`, when one exists (it is then unique up to a.e. equality on
`Ω`, as the book notes after Definition 3.1); a chosen representative. When `f` has no weak
`∂^α` on `Ω` the value is the junk function `0`: every use in this development is guarded by a
hypothesis that the weak derivative exists. -/
noncomputable def weakDeriv {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (α : Fin n → ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) : EuclideanSpace ℝ (Fin n) → ℝ :=
  if h : ∃ g, HasWeakDeriv Ω α f g then h.choose else 0

/-- The pointwise Euclidean length `|Df(x)| = (∑ᵢ (∂ᵢ f(x))²)^{1/2}` of the weak gradient of `f`
on `Ω`, where `∂ᵢ f = weakDeriv Ω (Pi.single i 1) f` is the weak first partial derivative. -/
noncomputable def weakGradNorm {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.sqrt (∑ i : Fin n, (weakDeriv Ω (Pi.single i 1) f x) ^ 2)

end HunterPDE.Shared
