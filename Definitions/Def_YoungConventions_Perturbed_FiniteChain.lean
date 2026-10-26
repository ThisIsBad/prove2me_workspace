import Mathlib

open Finset

namespace YoungConventions.Perturbed

/-!
Finite Markov chains: aperiodicity, stationary distributions, reachability, recurrent states and
the recurrent communication classes.
Young (1993), *The Evolution of Conventions*, Econometrica 61:57–84, Appendix, pp. 77–78
(PDF pp. 22–23).

**Formalization Note.** A Markov chain on the finite state space `X` is its transition matrix
`A : Matrix X X ℝ`, with `A x y` the probability of the one-period transition `x → y`; row
stochasticity (`A ∈ Matrix.rowStochastic ℝ X`) is stated where it is assumed. Distributions are
row vectors `μ : X → ℝ`, so stationarity is `μ A = μ`. Mathlib supplies irreducibility
(`Matrix.IsIrreducible`) but not aperiodicity, which is defined here.
-/

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Aperiodicity (Young 1993, Appendix, condition (6), p. 77, PDF p. 22): every state `x` has
period `1`, i.e. the only natural number dividing every return time `n ≥ 1` with
`(A ^ n) x x > 0` is `1` (the greatest common divisor of the return times is `1`).

**Formalization Note.** The period of `x` is the gcd of `{n ≥ 1 | (Aⁿ)ₓₓ > 0}`; "gcd = 1" is
written as "every common divisor equals 1". A state with no return times has gcd `0` and is not
aperiodic. -/
def IsAperiodic (A : Matrix X X ℝ) : Prop :=
  ∀ x : X, ∀ d : ℕ, (∀ n : ℕ, 1 ≤ n → 0 < (A ^ n) x x → d ∣ n) → d = 1

/-- `μ` is a stationary distribution of the chain `A` (Young 1993, Appendix, p. 77, PDF p. 22):
`μ` is a probability vector on `X` (nonnegative, summing to `1`) and `μ A = μ`, i.e.
`∑ₓ μ x · A x y = μ y` for every `y`. -/
def IsStationaryDist (A : Matrix X X ℝ) (μ : X → ℝ) : Prop :=
  (∀ x, 0 ≤ μ x) ∧ ∑ x, μ x = 1 ∧ ∀ y, ∑ x, μ x * A x y = μ y

/-- `y` is reachable from `x` under `A`: `(Aⁿ) x y > 0` for some `n ≥ 0` (`n = 0` allowed, so
every state reaches itself). -/
def Reaches (A : Matrix X X ℝ) (x y : X) : Prop :=
  ∃ n : ℕ, 0 < (A ^ n) x y

/-- `x` is a recurrent state of `A`: every state reachable from `x` can reach `x` back. -/
def IsRecurrentState (A : Matrix X X ℝ) (x : X) : Prop :=
  ∀ y, Reaches A x y → Reaches A y x

open Classical in
/-- The communication class of `x`: the states `y` with `x ⇝ y` and `y ⇝ x`. -/
noncomputable def commClass (A : Matrix X X ℝ) (x : X) : Finset X :=
  univ.filter (fun y => Reaches A x y ∧ Reaches A y x)

open Classical in
/-- The recurrent communication classes `X₁, …, X_J` of `A` (Young 1993, Appendix, pp. 77–78,
PDF pp. 22–23): the distinct communication classes of recurrent states.

**Formalization Note.** This is the standard definition; the paper's characterization (i)–(iii)
on pp. 77–78 is a consequence and is not used as the definition. The classes are a
`Finset (Finset X)`, so they are distinct by construction; the index set `{1, …, J}` is the
subtype `RecClass A`. -/
noncomputable def recurrentClasses (A : Matrix X X ℝ) : Finset (Finset X) :=
  (univ.filter (fun x => IsRecurrentState A x)).image (commClass A)

/-- The index type `{1, …, J}` of the recurrent communication classes of `A`. -/
abbrev RecClass (A : Matrix X X ℝ) : Type _ :=
  {C : Finset X // C ∈ recurrentClasses A}

end YoungConventions.Perturbed
