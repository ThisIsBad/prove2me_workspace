import Definitions.Def_mm_basic

/-!
Markov chain Monte Carlo: the Metropolis and Glauber chains, following
Levin–Peres–Wilmer, *Markov Chains and Mixing Times*, Chapter 3.

Given a target distribution `π`, these constructions produce transition
matrices having `π` as a stationary distribution.
-/

namespace MarkovMixing

noncomputable section

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The **Metropolis chain** for a target distribution `π` and a symmetric
base chain `Ψ`: a move proposed by `Ψ` from `x` to `y ≠ x` is accepted with
probability `1 ∧ π(y)/π(x)` (LPW §3.2.1). -/
def metropolis (Ψ : Matrix V V ℝ) (π : V → ℝ) : Matrix V V ℝ :=
  fun x y =>
    if y = x then 1 - ∑ z ∈ ({x}ᶜ : Finset V), Ψ x z * min 1 (π z / π x)
    else Ψ x y * min 1 (π y / π x)

/-- The **Metropolized chain** for a target distribution `π` and a general
(not necessarily symmetric) base chain `Ψ`: a move proposed by `Ψ` from `x`
to `y ≠ x` is accepted with probability
`(π(y)Ψ(y,x)) / (π(x)Ψ(x,y)) ∧ 1` (LPW §3.2.2, Eq. (3.5)). -/
def metropolized (Ψ : Matrix V V ℝ) (π : V → ℝ) : Matrix V V ℝ :=
  fun x y =>
    if y = x then
      1 - ∑ z ∈ ({x}ᶜ : Finset V), Ψ x z * min 1 (π z * Ψ z x / (π x * Ψ x z))
    else Ψ x y * min 1 (π y * Ψ y x / (π x * Ψ x y))

/-- The (single-site) **Glauber dynamics** for a distribution `π` on a space
of configurations `Vv → S`: pick a vertex `v` uniformly at random, then
re-sample the value at `v` from `π` conditioned on agreeing with the current
configuration off `v` (LPW §3.3.2, Eq. (3.6)).  Rows at configurations
outside the support of `π` are junk. -/
def glauber {Vv S : Type*} [Fintype Vv] [DecidableEq Vv] [Fintype S] [DecidableEq S]
    (π : (Vv → S) → ℝ) : Matrix (Vv → S) (Vv → S) ℝ :=
  fun x y =>
    (Fintype.card Vv : ℝ)⁻¹ *
      ∑ v : Vv,
        if ∀ w : Vv, w ≠ v → y w = x w then
          π y / ∑ z ∈ Finset.univ.filter (fun z : Vv → S => ∀ w : Vv, w ≠ v → z w = x w), π z
        else 0

end

end MarkovMixing
