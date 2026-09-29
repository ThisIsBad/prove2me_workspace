import Mathlib
import Definitions.Def_SupportVectorMachines_InfiniteSample_Loss

open MeasureTheory

namespace SupportVectorMachines.InfiniteSample

/-- The **`L`-risk** of `f` with respect to a distribution `P` on `X × ℝ` (Definition 2.2, p. 22,
restated locally per Hard Rule 9), represented as the lower Lebesgue integral (`lintegral`) of
the nonnegative integrand `L(x,y,f(x))` into `ℝ≥0∞`, which — since `L ≥ 0` — always exists and
equals the book's `R_{L,P}(f) := ∫ L(x,y,f(x)) dP(x,y)` exactly, finite or not ("the above
integral … always exists, although it is not necessarily finite", p. 23), with no integrability
hypothesis needed. -/
noncomputable def populationRisk {X : Type*} [MeasurableSpace X] (L : Loss X)
    (P : Measure (X × ℝ)) (f : X → ℝ) : ENNReal :=
  ∫⁻ p, ENNReal.ofReal (L p.1 p.2 (f p.1)) ∂P

/-- The **empirical `L`-risk** of `f` with respect to a sample `D : Fin n → X × ℝ` (Definition
2.2, Eq. (2.1), p. 23): `R_{L,D}(f) := (1/n) ∑ᵢ L(xᵢ,yᵢ,f(xᵢ))`, the risk with respect to the
empirical measure `D̄ := (1/n) ∑ᵢ δ_{(xᵢ,yᵢ)}`. -/
noncomputable def empiricalRisk {X : Type*} (n : ℕ) (L : Loss X) (D : Fin n → X × ℝ)
    (f : X → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, L (D i).1 (D i).2 (f (D i).1)

end SupportVectorMachines.InfiniteSample
