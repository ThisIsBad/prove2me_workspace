import Mathlib
import Definitions.Def_SolomonRWRE_DiffEq_System

open MeasureTheory ProbabilityTheory Filter Topology

namespace SolomonRWRE.DiffEq

/-- **Proof of Theorem (4.4), p. 29** (unnumbered): a.e.
`lim inf_{n→∞} (Z_1 + ⋯ + Z_n)/n ≥ Σ_{k=1}^∞ ν^k` (by Fatou's lemma); this proves (4.4) when
`ν ≥ 1`.

**Formalization Note.** In `[0, ∞]`; the series `Σ_{k≥1} ν^k` is the `tsum` of `ν^(k+1)`
over `k : ℕ` (index shift), and equals `∞` when `ν ≥ 1`. No hypothesis on `ν`, as on the
page. -/
theorem proof_4_4_liminf {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (σ : ℕ → Ω → ℝ) (hσ : IsIIDNonneg P σ) :
    ∀ᵐ ω ∂P, ∑' k : ℕ, nu P σ ^ (k + 1) ≤
      liminf (fun n : ℕ => ENNReal.ofReal ((∑ m ∈ Finset.Icc 1 n, Z σ m ω) / n)) atTop := by sorry

end SolomonRWRE.DiffEq

