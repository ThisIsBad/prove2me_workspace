import Mathlib
import Definitions.Def_PalmQueueing_Loynes_Coupling

/-!
# Theorem 2.4.1: coupling implies convergence in variation (§2.4.1, p.99)
-/

namespace PalmQueueing.Loynes

open MeasureTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Theorem 2.4.1** (§2.4.1, p.99). If `{X_n}` couples with a `θ`-compatible sequence
`{Z ∘ θⁿ}`, then the sequence `{X_{n+k}}_{n ≥ 0}` converges in variation to `{Z ∘ θⁿ}` as `k`
tends to `∞`:

`(2.4.1)  lim_{k→∞} | P̃_{X,k} − P̃_{Z,k} | = 0`,

where `P̃_{X,k}` is the law on `(E^∞, E^∞)` of the whole shifted trajectory
`X̃_k = (X_k, X_{k+1}, …)`.

The convergence is **in variation on the law of the entire trajectory**, not of one coordinate and
not in distribution: `|P̃_{X,k} − P̃_{Z,k}| = sup_{C} |P̃_{X,k}(C) − P̃_{Z,k}(C)|` over all
measurable `C ⊆ E^∞`. That is why it is stated with the set quantified inside the index `K`, which
is exactly the supremum being small. The book derives it from the **coupling inequality**
`(2.4.2) |P̃_{X,k} − P̃_{Z,k}| ≤ P(N > k)`, which is finite-`N` plus nothing else.

`E` is any measurable space here. p.99 takes `(E, ℰ)` Polish with its Borel field and introduces
the metric `d_∞` on `E^∞` only to identify that space's Borel field with the product σ-field; the
statement uses the product σ-field directly, so the metric is not needed. -/
theorem coupling_convergence {E : Type*} [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (θ : Ω → Ω) (X Z : ℕ → Ω → E)
    (hXmeas : ∀ n, Measurable (X n)) (hZmeas : ∀ n, Measurable (Z n))
    (hZcomp : IsShiftCompatible θ Z)
    (hcouple : Couple P X Z) :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      ∀ C : Set (ℕ → E), MeasurableSet C →
        |(P {ω | (fun n : ℕ => X (n + k) ω) ∈ C}).toReal
          - (P {ω | (fun n : ℕ => Z (n + k) ω) ∈ C}).toReal| ≤ ε := by sorry

end PalmQueueing.Loynes

