import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_mm_lower
import Definitions.Def_mm_continuous

namespace LogSobolevMC.ChiSquare

noncomputable section

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The Dirichlet form `ℰ(f, g) = ⟨(I − K)f, g⟩ = Σ_x (f(x) − Kf(x)) g(x) π(x)` (§2.3, p. 705).
Bilinear, not symmetric for nonreversible `K`; the order of the arguments is the paper's. -/
def dirichlet (K : Matrix V V ℝ) (π : V → ℝ) (f g : V → ℝ) : ℝ :=
  ∑ x, (f x - K.mulVec f x) * g x * π x

/-- The norm `‖f‖_p = (Σ_x |f(x)|^p π(x))^{1/p}` of `ℓᵖ(π)`, for a real exponent `p`
(§2.1, p. 701; the paper uses `1 ≤ p`). -/
def lpNorm (π : V → ℝ) (p : ℝ) (f : V → ℝ) : ℝ :=
  (∑ x, |f x| ^ p * π x) ^ (1 / p)

/-- `ℒ(f) = Σ_x |f(x)|² log(|f(x)|² / ‖f‖₂²) π(x)` (§3.1, p. 714). With `Real.log 0 = 0`, the
terms with `f(x) = 0` vanish (the convention `0 log 0 = 0`). -/
def entL (π : V → ℝ) (f : V → ℝ) : ℝ :=
  ∑ x, |f x| ^ (2 : ℝ) * Real.log (|f x| ^ (2 : ℝ) / lpNorm π 2 f ^ (2 : ℝ)) * π x

/-- `ℒ_p(f) = Σ_x |f(x)|^p log(|f(x)|^p / ‖f‖_p^p) π(x)` (proof of Theorem 3.5, p. 721). -/
def entLp (π : V → ℝ) (p : ℝ) (f : V → ℝ) : ℝ :=
  ∑ x, |f x| ^ p * Real.log (|f x| ^ p / lpNorm π p f ^ p) * π x

/-- The spectral gap `λ = min {ℰ(f, f)/Var(f) : Var(f) ≠ 0}` of (2.4), p. 706, as a real `sInf`;
variational, so it is the paper's `λ` also for nonreversible chains. -/
def gap (K : Matrix V V ℝ) (π : V → ℝ) : ℝ :=
  sInf {r : ℝ | ∃ f : V → ℝ,
    MarkovMixing.distVar π f ≠ 0 ∧ r = dirichlet K π f f / MarkovMixing.distVar π f}

/-- The log-Sobolev constant `α = inf {ℰ(f, f)/ℒ(f) : ℒ(f) ≠ 0}` of (3.1), p. 714, as a real `sInf`. -/
def logSobolev (K : Matrix V V ℝ) (π : V → ℝ) : ℝ :=
  sInf {r : ℝ | ∃ f : V → ℝ, entL π f ≠ 0 ∧ r = dirichlet K π f f / entL π f}

/-- `H_t = e^{−t(I−K)}` acting on a function, `H_t f(x) = Σ_y H_t(x, y) f(y)` (§2.1, p. 702). -/
def heatOp (K : Matrix V V ℝ) (t : ℝ) (f : V → ℝ) : V → ℝ :=
  (MarkovMixing.heatKernel K t).mulVec f

/-- The density `h_t^x(y) = H_t(x, y)/π(y)` of `H_t^x` with respect to `π` (§2.1, p. 702). -/
def density (K : Matrix V V ℝ) (π : V → ℝ) (t : ℝ) (x : V) : V → ℝ :=
  fun y => MarkovMixing.heatKernel K t x y / π y

end

end LogSobolevMC.ChiSquare
