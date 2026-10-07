import Mathlib
import Definitions.Def_PalmQueueing_Recurrence_Renovating

/-!
# Theorem 2.5.3: Borovkov's renovating-events theorem (§2.5.4, p.115)
-/

namespace PalmQueueing.Recurrence

open MeasureTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Theorem 2.5.3** (p.115), Borovkov's sufficient condition for a finite stationary regime of
`(2.5.1)` to exist and for strong backwards coupling to occur.

If `{W_n}` admits a sequence of renovating events `{A_n}`, `n ≥ 0`, all with the same length
`m ≥ 1` and the same associated function `Φ`, and if

`(2.5.15)  lim_{n→∞} P⁰[ ⋂_{k=0}^{∞} ⋃_{l=0}^{n} A_l ∩ θ^k A_{l+k} ] = 1`,

then `W_n ∘ θ^{-n}` converges a.s. to a finite limit `Z` as `n` tends to `∞`. The random variable
`Z` satisfies the relation `Z ∘ θ = h(Z, ξ)`, and `{W_n}` couples in the strong backwards sense
with `{Z ∘ θⁿ}`.

All three conclusions are stated: convergence, the fixed-point relation that makes `Z` a
stationary solution, and strong backwards coupling — which is strictly stronger than the
convergence and is what the theorem is quoted for.

The nesting in (2.5.15) is the intersection over **all** `k ≥ 0` of the union over `l ≤ n`; only
the union is truncated at `n`.

`herg` is the standing assumption of §2.5.1 (p.104): `(P⁰, θ)` is ergodic (in particular `θ`
preserves `P⁰`, which the proof uses in `P⁰[⋂ B_{n,k}] = P⁰[⋂ θ^{-n} B_{n,k}]`). The relation
`Z ∘ θ = h(Z, ξ)` is an equality of random variables, i.e. `P⁰`-a.s. `θ^k A_{l+k}` is the image of `A_{l+k}` under the `k`-th iterate of
the shift, under which reading (2.5.15) reduces to Borovkov's classical
`lim_n P⁰[⋃_{l≤n} A_l] = 1` for stationary renovating events. -/
theorem borovkov_renovating {E F : Type*} [MeasurableSpace E] [TopologicalSpace E]
    (P0 : Measure Ω) [IsProbabilityMeasure P0] (θ : Ω ≃ᵐ Ω) (herg : Ergodic θ P0)
    (h : E → F → E) (xi : ℕ → Ω → F) (xi0 : Ω → F)
    (hxi : ∀ (n : ℕ) (ω : Ω), xi n ω = xi0 ((θ : Ω → Ω)^[n] ω))
    (Y : Ω → E) (W : ℕ → Ω → E) (hW : IsRecurrentSequence h xi Y W)
    (m : ℕ) (Phi : (Fin m → F) → E) (A : ℕ → Set Ω)
    (hA : ∀ n, MeasurableSet (A n)) (hren : IsRenovating xi W m Phi A)
    (hcond : Tendsto
      (fun n : ℕ => P0 (⋂ k : ℕ, ⋃ l ∈ Finset.range (n + 1), A l ∩ shiftImage θ k (A (l + k))))
      atTop (𝓝 1)) :
    ∃ Z : Ω → E,
      (∀ᵐ ω ∂P0, Tendsto (fun n : ℕ => W n ((θ.symm^[n]) ω)) atTop (𝓝 (Z ω))) ∧
      (∀ᵐ ω ∂P0, Z ((θ : Ω → Ω) ω) = h (Z ω) (xi0 ω)) ∧
      StrongBackwardsCoupling P0 θ W Z := by sorry

end PalmQueueing.Recurrence

