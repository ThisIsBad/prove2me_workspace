import Mathlib
import Definitions.Def_RadGauss_Kernel_Complexity
import Definitions.Def_RadGauss_Kernel_KernelClass

namespace RadGauss.Kernel

/-- Lemma 22 (Bartlett–Mendelson 2002, p. 477). Let `k` be a kernel on `𝒳`, `B ≥ 0`, and let
`F = kernelClass k B`. For every sample `x_1, …, x_n ∈ 𝒳`,
`Ĝ_n(F) ≤ (2B/n) √(Σ_i k(x_i, x_i))` and `R̂_n(F) ≤ (2B/n) √(Σ_i k(x_i, x_i))`.
The paper takes `B > 0`; `0 ≤ B` is assumed here. At `n = 0` both sides are `0`. -/
theorem lemma_22 {X : Type*} [TopologicalSpace X] (k : X → X → ℝ) (hk : IsKernel k)
    (B : ℝ) (hB : 0 ≤ B) (n : ℕ) (x : Fin n → X) :
    empiricalGaussian (kernelClass k B) n x
        ≤ ENNReal.ofReal (2 * B / n * Real.sqrt (∑ i, k (x i) (x i))) ∧
      RadGauss.Classification.empiricalRademacher (kernelClass k B) n x
        ≤ ENNReal.ofReal (2 * B / n * Real.sqrt (∑ i, k (x i) (x i))) := by sorry

end RadGauss.Kernel

