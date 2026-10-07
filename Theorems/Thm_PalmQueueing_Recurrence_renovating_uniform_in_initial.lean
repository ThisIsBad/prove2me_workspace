import Mathlib
import Definitions.Def_PalmQueueing_Recurrence_Renovating

/-!
# Corollary 2.5.1: a stationary limit that does not depend on the initial condition (§2.5.4, p.118)
-/

namespace PalmQueueing.Recurrence

open MeasureTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Corollary 2.5.1** (p.118). Let `𝒴` be a set of random variables, and consider the sequences
`{W_n^{[Y]}}` for all possible initial conditions `Y` in `𝒴`. If there exists a sequence of events
`{A_n}` compatible with the shift and satisfying the condition `P⁰(A_0) > 0`, a function `Φ` and
an integer `m`, such that `{A_n}` renovates `{W_n^{[Y]}}` with length `m` and function `Φ` **for
all `Y ∈ 𝒴` at once**, then there exists a stationary sequence `{Z ∘ θⁿ}`, solution of (2.5.1),
and such that for all `Y ∈ 𝒴`, the sequence `{W_n^{[Y]}}` converges with strong backwards coupling
to `{Z ∘ θⁿ}`.

The strengthening over Theorem 2.5.3 is that the **limit `Z` does not depend on `Y`**: one
stationary regime, reached from every initial condition in `𝒴`. The proof replaces (2.5.17) by

`(2.5.22)  ⋂_{k=0}^{∞} B_{n,k} ⊂ { W_n^{[Y*]} ∘ θ^{-n} = W_{n+k}^{[Y]} ∘ θ^{-n-k},
             ∀k ≥ 0, ∀Y ∈ 𝒴 }`

for an arbitrary `Y* ∈ 𝒴`. Remark 2.5.3 draws the uniqueness consequence: two finite solutions
admitting the same renovating events and the same `Φ` are equal.

One correction to the page. The corollary prints the renovating condition as
"on `A_n`, `W_n^{[Y]} = Φ(ξ_n, …, ξ_{n+m-1})`", with `W_n` where the definition of a renovating
event on p.115 has `W_{n+m}`: `(2.5.14) W_{n+m} = Φ(ξ_n, …, ξ_{n+m-1})`. With `W_n` the left side
would depend on `ξ_n, …, ξ_{n+m-1}`, all of which are in its future under
`W_{n+1} = h(W_n, ξ_n)`. The statement here uses `IsRenovating`, that is `W_{n+m}`; the page's
text is quoted verbatim in the milestone.

`herg` is the standing assumption of §2.5.1 (p.104), `(P⁰, θ)` ergodic, which the proof uses
through Property 2.5.5 to turn `P⁰(A_0) > 0` into (2.5.15). `𝒴` is nonempty, as the proof's
"`Y*` an arbitrary element of `𝒴`" presupposes; with `𝒴 = ∅` the corollary would assert that
every recurrence has a stationary solution. -/
theorem renovating_uniform_in_initial {E F : Type*} [MeasurableSpace E] [TopologicalSpace E]
    (P0 : Measure Ω) [IsProbabilityMeasure P0] (θ : Ω ≃ᵐ Ω) (herg : Ergodic θ P0)
    (h : E → F → E) (xi : ℕ → Ω → F) (xi0 : Ω → F)
    (hxi : ∀ (n : ℕ) (ω : Ω), xi n ω = xi0 ((θ : Ω → Ω)^[n] ω))
    (Yset : Set (Ω → E)) (hYne : Yset.Nonempty) (W : (Ω → E) → ℕ → Ω → E)
    (hW : ∀ Y ∈ Yset, IsRecurrentSequence h xi Y (W Y))
    (m : ℕ) (Phi : (Fin m → F) → E) (A : ℕ → Set Ω)
    (hA : ∀ n, MeasurableSet (A n))
    (hcompat : ∀ n : ℕ, A n = ((θ : Ω → Ω)^[n]) ⁻¹' A 0)
    (hpos : 0 < P0 (A 0))
    (hren : ∀ Y ∈ Yset, IsRenovating xi (W Y) m Phi A) :
    ∃ Z : Ω → E,
      (∀ᵐ ω ∂P0, Z ((θ : Ω → Ω) ω) = h (Z ω) (xi0 ω)) ∧
      ∀ Y ∈ Yset,
        (∀ᵐ ω ∂P0, Tendsto (fun n : ℕ => W Y n ((θ.symm^[n]) ω)) atTop (𝓝 (Z ω))) ∧
        StrongBackwardsCoupling P0 θ (W Y) Z := by sorry

end PalmQueueing.Recurrence

