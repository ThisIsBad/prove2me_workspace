import Definitions.Def_mm_mixing
import Definitions.Def_mm_lower

/-!
Eigenvalues, spectral gap, relaxation time, and Dirichlet forms, following
Levin–Peres–Wilmer, *Markov Chains and Mixing Times*, Chapters 12–13.

Eigenfunctions are right eigenvectors: `P f = λ f` with
`(Pf)(x) = ∑_y P(x,y) f(y)`.  For a chain reversible with respect to `π`,
all eigenvalues are real and `ℓ²(π)` has an orthonormal eigenbasis
(Lemma 12.2), so the definitions below capture the whole spectrum.
-/

namespace MarkovMixing

noncomputable section

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `λ` is an **eigenvalue** of `P`, with a (real) eigenfunction
(LPW §12.1). -/
def IsEigenvalue (P : Matrix V V ℝ) (lam : ℝ) : Prop :=
  ∃ f : V → ℝ, f ≠ 0 ∧ P.mulVec f = lam • f

/-- `λ₂`, the largest eigenvalue different from `1` (for an irreducible
reversible chain, the second largest eigenvalue; LPW §12.2). -/
def lambdaTwo (P : Matrix V V ℝ) : ℝ :=
  sSup {lam : ℝ | IsEigenvalue P lam ∧ lam ≠ 1}

/-- `λ⋆ = max {|λ| : λ an eigenvalue of P, λ ≠ 1}` (LPW §12.2). -/
def lambdaStar (P : Matrix V V ℝ) : ℝ :=
  sSup {r : ℝ | ∃ lam : ℝ, IsEigenvalue P lam ∧ lam ≠ 1 ∧ r = |lam|}

/-- The **spectral gap** `γ = 1 − λ₂` (LPW §12.2). -/
def spectralGap (P : Matrix V V ℝ) : ℝ :=
  1 - lambdaTwo P

/-- The **absolute spectral gap** `γ⋆ = 1 − λ⋆` (LPW §12.2). -/
def absSpectralGap (P : Matrix V V ℝ) : ℝ :=
  1 - lambdaStar P

/-- The **relaxation time** `t_rel = 1/γ⋆` (LPW §12.2). -/
def relaxationTime (P : Matrix V V ℝ) : ℝ :=
  (absSpectralGap P)⁻¹

/-- The inner product `⟨f,g⟩_π = ∑_x f(x) g(x) π(x)` on `ℓ²(π)`
(LPW §12.1, Eq. (12.1)). -/
def innerPi (π : V → ℝ) (f g : V → ℝ) : ℝ :=
  ∑ x, f x * g x * π x

/-- The **Dirichlet form**
`E(f) = ½ ∑_{x,y} [f(x) − f(y)]² π(x) P(x,y)` (LPW §13.3,
Eq. (13.11)). -/
def dirichletForm (P : Matrix V V ℝ) (π : V → ℝ) (f : V → ℝ) : ℝ :=
  2⁻¹ * ∑ x, ∑ y, (f x - f y) ^ 2 * (π x * P x y)

/-- Simple random walk on the `n`-cycle `ℤ_n` (LPW §12.3.1; take `n ≥ 3`). -/
def cycleWalk (n : ℕ) : Matrix (ZMod n) (ZMod n) ℝ :=
  fun x y => if y = x + 1 ∨ y = x - 1 then 1 / 2 else 0

end

end MarkovMixing
