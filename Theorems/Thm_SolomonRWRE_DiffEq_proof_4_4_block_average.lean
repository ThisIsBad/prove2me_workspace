import Mathlib
import Definitions.Def_SolomonRWRE_DiffEq_System

open MeasureTheory ProbabilityTheory Filter Topology

namespace SolomonRWRE.DiffEq

/-- **Proof of Theorem (4.4), pp. 28–29** (unnumbered): for `k` fixed,
`lim_{n→∞} Y_k^n / n = ν^k` a.e.

**Formalization Note.** The limit is taken in `[0, ∞]` (via `ENNReal.ofReal`, harmless since
`Y_k^n ≥ 0`), because `ν = E(σ)` may be `∞`, and then `ν^k = ∞`. `k ≥ 1` as on the page
(the products have `k` factors). -/
theorem proof_4_4_block_average {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (σ : ℕ → Ω → ℝ) (hσ : IsIIDNonneg P σ) (k : ℕ) (hk : 1 ≤ k) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => ENNReal.ofReal (Y σ k n ω / n)) atTop
      (𝓝 (nu P σ ^ k)) := by sorry

end SolomonRWRE.DiffEq

