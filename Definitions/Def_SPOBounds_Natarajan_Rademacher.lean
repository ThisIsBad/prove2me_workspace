import Mathlib
import Definitions.Def_SPOBounds_Natarajan_Model

open MeasureTheory

namespace SPOBounds.Natarajan

/-- The SPO risk `R_SPO(f) = 𝔼_{(x,c)∼D}[ℓ_SPO(f(x), c)]` (p. 6). -/
noncomputable def spoRisk {d : ℕ} {X : Type*} [MeasurableSpace X]
    (D : Measure (X × EuclideanSpace ℝ (Fin d)))
    (w : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (f : X → EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∫ z, spoLoss w (f z.1) z.2 ∂D

/-- The empirical SPO risk `R̂_SPO(f) = (1/n) ∑ᵢ ℓ_SPO(f(xᵢ), cᵢ)` on the sample `s` (p. 6). -/
noncomputable def empRisk {d n : ℕ} {X : Type*}
    (w : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (f : X → EuclideanSpace ℝ (Fin d)) (s : Fin n → X × EuclideanSpace ℝ (Fin d)) : ℝ :=
  (1 / n : ℝ) * ∑ i, spoLoss w (f (s i).1) (s i).2

/-- For a fixed sign vector `σ ∈ {±1}ⁿ` (`true ↦ +1`, `false ↦ −1`), the supremum
`sup_{f ∈ H} (1/n) ∑ᵢ σᵢ ℓ_SPO(f(xᵢ), cᵢ)` on the sample `s`. -/
noncomputable def signedSup {d n : ℕ} {X : Type*}
    (w : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (H : Set (X → EuclideanSpace ℝ (Fin d))) (σ : Fin n → Bool)
    (s : Fin n → X × EuclideanSpace ℝ (Fin d)) : ℝ :=
  ⨆ f : H, (1 / n : ℝ) * ∑ i, (if σ i then (1 : ℝ) else -1) * spoLoss w ((f : X → _) (s i).1) (s i).2

/-- The empirical Rademacher complexity of `H` with respect to the SPO loss (p. 8):
`R̂ⁿ_SPO(H) = 𝔼_σ[sup_{f ∈ H} (1/n) ∑ᵢ σᵢ ℓ_SPO(f(xᵢ), cᵢ)]`, the expectation over i.i.d.
uniform signs written as the average over all `2ⁿ` sign vectors. -/
noncomputable def empRademacherSPO {d n : ℕ} {X : Type*}
    (w : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (H : Set (X → EuclideanSpace ℝ (Fin d))) (s : Fin n → X × EuclideanSpace ℝ (Fin d)) : ℝ :=
  (1 / 2 ^ n : ℝ) * ∑ σ : Fin n → Bool, signedSup w H σ s

/-- The expected Rademacher complexity `ℜⁿ_SPO(H) = 𝔼[R̂ⁿ_SPO(H)]` over an i.i.d. sample of
size `n` from `D` (p. 9), as a Bochner integral against the product measure `Dⁿ`. -/
noncomputable def expRademacherSPO {d : ℕ} {X : Type*} [MeasurableSpace X]
    (D : Measure (X × EuclideanSpace ℝ (Fin d)))
    (w : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (H : Set (X → EuclideanSpace ℝ (Fin d))) (n : ℕ) : ℝ :=
  ∫ s, empRademacherSPO w H s ∂(Measure.pi fun _ : Fin n => D)

/-- The uniform deviation `sup_{f ∈ H} (R_SPO(f) − R̂_SPO(f))` on the sample `s`; it appears
only in a measurability hypothesis. -/
noncomputable def supDeviation {d n : ℕ} {X : Type*} [MeasurableSpace X]
    (D : Measure (X × EuclideanSpace ℝ (Fin d)))
    (w : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (H : Set (X → EuclideanSpace ℝ (Fin d))) (s : Fin n → X × EuclideanSpace ℝ (Fin d)) : ℝ :=
  ⨆ f : H, (spoRisk D w f - empRisk w f s)

end SPOBounds.Natarajan
