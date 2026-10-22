import Mathlib

open MeasureTheory

namespace BigDataNV.Reg

/-- Theorem 6, p. 31: a two-sided generalization bound for any algorithm that is uniformly stable
(with parameter `α`) and whose loss is bounded in `[0, M]`. The data space is `Z`, its support is
`Z0`, `A` maps a sample of size `n` to a hypothesis in `H`, and `Aloo i S` is the comparison
hypothesis that ignores the `i`-th observation. -/
theorem theorem6_two_sided_bound {Z H : Type*} [MeasurableSpace Z]
    (μ : Measure Z) [IsProbabilityMeasure μ] (Z0 : Set Z) (hμ : μ Z0ᶜ = 0)
    (ℓ : H → Z → ℝ) (n : ℕ) (hn : 1 ≤ n) (A : (Fin n → Z) → H)
    (Aloo : Fin n → (Fin n → Z) → H)
    (hloo : ∀ (i : Fin n) (S S' : Fin n → Z), (∀ j, j ≠ i → S j = S' j) → Aloo i S = Aloo i S')
    (α M : ℝ)
    (hstab : ∀ S : Fin n → Z, (∀ j, S j ∈ Z0) → ∀ i : Fin n, ∀ z ∈ Z0,
      |ℓ (A S) z - ℓ (Aloo i S) z| ≤ α)
    (hbound : ∀ S : Fin n → Z, (∀ j, S j ∈ Z0) → ∀ z ∈ Z0, 0 ≤ ℓ (A S) z ∧ ℓ (A S) z ≤ M)
    (hmeas : Measurable (fun q : (Fin n → Z) × Z => ℓ (A q.1) q.2))
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (Measure.pi fun _ : Fin n => μ)
      {S | 2 * α + (4 * (n : ℝ) * α + M) * Real.sqrt (Real.log (2 / δ) / (2 * (n : ℝ))) <
        |(∫ z, ℓ (A S) z ∂μ) - (1 / (n : ℝ)) * ∑ i, ℓ (A S) (S i)|} ≤ ENNReal.ofReal δ := by sorry

end BigDataNV.Reg

