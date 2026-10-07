import Definitions.Def_mm_mixing
import Definitions.Def_mm_spectral
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
Continuous-time chains, following Levin–Peres–Wilmer, *Markov Chains and
Mixing Times*, Chapter 20.

The heat kernel is defined by Poissonization (LPW Eq. (20.5)):
`H_t(x,y) = ∑_k e^{-t} t^k/k! · P^k(x,y)`, which agrees with the matrix
exponential `e^{t(P−I)}`.
-/

namespace MarkovMixing

noncomputable section

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The **heat kernel** `H_t = e^{t(P−I)}`, via the Poissonization formula
(LPW §20.1, Eq. (20.5)). -/
def heatKernel (P : Matrix V V ℝ) (t : ℝ) : Matrix V V ℝ :=
  fun x y => ∑' k : ℕ, Real.exp (-t) * t ^ k / (Nat.factorial k) * (P ^ k) x y

/-- `d^{cont}(t) = max_x ‖H_t(x,·) − π‖_TV` (LPW §20.2). -/
def contDistStationary (P : Matrix V V ℝ) (π : V → ℝ) (t : ℝ) : ℝ :=
  ⨆ x : V, tvDist (fun y => heatKernel P t x y) π

/-- The continuous mixing time
`t^{cont}_mix(ε) = inf {t ≥ 0 : d^{cont}(t) ≤ ε}` (LPW §20.2,
Eq. (20.7)). -/
def contMixingTime (P : Matrix V V ℝ) (π : V → ℝ) (ε : ℝ) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ contDistStationary P π t ≤ ε}

/-- The chain updating only coordinate `i` with the matrix `P i`
(LPW §20.4, Eq. (20.14)). -/
def coordChain {n : ℕ} {W : Fin n → Type*} [∀ i, Fintype (W i)]
    [∀ i, DecidableEq (W i)] (P : ∀ i, Matrix (W i) (W i) ℝ) (i : Fin n) :
    Matrix (∀ j, W j) (∀ j, W j) ℝ :=
  fun x y => if ∀ j : Fin n, j ≠ i → y j = x j then P i (x i) (y i) else 0

/-- The **product chain** `P = n⁻¹ ∑ᵢ P̃ᵢ`: pick a coordinate uniformly at
random and update it (LPW §20.4). -/
def productChain {n : ℕ} {W : Fin n → Type*} [∀ i, Fintype (W i)]
    [∀ i, DecidableEq (W i)] (P : ∀ i, Matrix (W i) (W i) ℝ) :
    Matrix (∀ j, W j) (∀ j, W j) ℝ :=
  fun x y => (n : ℝ)⁻¹ * ∑ i : Fin n, coordChain P i x y

end

end MarkovMixing
