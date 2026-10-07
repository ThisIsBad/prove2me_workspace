import Mathlib

/-!
# Borovkov's theory of renovating events (§2.5.4, pp.114-118)

A **stochastic recurrent sequence** on an ergodic shift `θ`,

`W_{n+1} = h(W_n, ξ_n)`,  with `{ξ_n}` compatible with the shift,

and the two notions Borovkov's theorem is about: a **renovating event**, on which the value of the
sequence `m` steps ahead is a fixed function of the intervening driving variables and so forgets
the past; and **strong backwards coupling**, which is what "reaches the stationary regime" means
here and is strictly stronger than backwards coupling.
-/

namespace PalmQueueing.Recurrence

open MeasureTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `{W_n}` is the stochastic recurrent sequence with initial condition `Y` driven by `{ξ_n}`
through `h` (p.114): `W_0 = Y` and `W_{n+1} = h(W_n, ξ_n)`. -/
def IsRecurrentSequence {E F : Type*} (h : E → F → E) (xi : ℕ → Ω → F) (Y : Ω → E)
    (W : ℕ → Ω → E) : Prop :=
  (∀ ω, W 0 ω = Y ω) ∧ ∀ (n : ℕ) (ω : Ω), W (n + 1) ω = h (W n ω) (xi n ω)

/-- `{ξ_n}` is compatible with the shift `θ`: `ξ_n = ξ_0 ∘ θⁿ`. -/
def IsDrivingSequence {F : Type*} (θ : Ω → Ω) (xi : ℕ → Ω → F) : Prop :=
  ∀ (n : ℕ) (ω : Ω), xi n ω = xi 0 (θ^[n] ω)

/-- `{A_n}` is a sequence of **renovating events** of length `m ≥ 1` with associated function
`Φ : F^m → E` for the stochastic recurrent sequence `{W_n}` (p.115): on `A_n`,

`(2.5.14)  W_{n+m} = Φ(ξ_n, …, ξ_{n+m-1})`.

On a renovating event the sequence's value `m` steps ahead does not depend on where it came from,
which is the whole mechanism. Events of the type `A_n = {W_n = 0}` are renovating of length `1`,
since on them `W_{n+1} = h(0, ξ_n)`. -/
def IsRenovating {E F : Type*} (xi : ℕ → Ω → F) (W : ℕ → Ω → E) (m : ℕ) (Phi : (Fin m → F) → E)
    (A : ℕ → Set Ω) : Prop :=
  1 ≤ m ∧ ∀ (n : ℕ) (ω : Ω), ω ∈ A n → W (n + m) ω = Phi fun l : Fin m => xi (n + l) ω

/-- **Strong backwards coupling** (2.5.12, p.114) occurs between `{W_n}` and the stationary
sequence `{Z ∘ θⁿ}` when

`N* = inf{ n ≥ 0 s.t. W_{n+k} ∘ θ^{-n-k} = Z, ∀ k ≥ 0 }`

is `P⁰`-a.s. finite — that is, when the sequence `W_n ∘ θ^{-n}` **is equal to** its limit `Z`
after a finite random index, not merely converging to it. The book is explicit that this is
stronger than backwards coupling. -/
def StrongBackwardsCoupling {E : Type*} (P0 : Measure Ω) (θ : Ω ≃ᵐ Ω) (W : ℕ → Ω → E)
    (Z : Ω → E) : Prop :=
  ∀ᵐ ω ∂P0, ∃ n : ℕ, ∀ k : ℕ, W (n + k) ((θ.symm^[n + k]) ω) = Z ω

/-- The set `θ^k A`, the image of `A` under the `k`-th iterate of the shift, as (2.5.15) writes
it. For a bijective `θ` this is `{ω : θ^{-k} ω ∈ A}`.

Read this way, (2.5.15) reduces to Borovkov's classical condition `lim_n P⁰[⋃_{l=0}^n A_l] = 1`
whenever the renovating events are stationary, `A_j = θ^{-j}A_0`: then `θ^k A_{l+k} = A_l` and the
intersection over `k` is `⋃_{l=0}^n A_l` itself. That agreement is what fixes the reading. -/
def shiftImage (θ : Ω ≃ᵐ Ω) (k : ℕ) (A : Set Ω) : Set Ω := (fun ω => (θ : Ω → Ω)^[k] ω) '' A

end PalmQueueing.Recurrence
