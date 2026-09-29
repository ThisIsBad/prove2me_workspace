import Mathlib

open MeasureTheory Filter Topology Set

namespace PorteusSS

/-- Convolution shorthand of §X: `conv f g y = ∫_{-∞}^{∞} f (y - x) g(x) dx` (Lebesgue integral
over `ℝ`; it is `0` when the integrand is not integrable, so every use below either assumes or
concludes integrability). -/
noncomputable def conv (f g : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ x, f (y - x) * g x

/-- Piecewise continuity on an interval `I` (§X): there is a finite set `A ⊆ I` such that
(i) `f` is continuous on `I \ A`, and (ii) at every point of `A` the one-sided limits of `f`
(within `I`) exist as real numbers whenever they are defined, i.e. whenever `I` has points
arbitrarily close to that side. -/
def PiecewiseContinuousOn (f : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∃ A : Finset ℝ, (↑A : Set ℝ) ⊆ I ∧ ContinuousOn f (I \ ↑A) ∧
    ∀ a ∈ A,
      ((𝓝[I ∩ Iio a] a).NeBot → ∃ l : ℝ, Tendsto f (𝓝[I ∩ Iio a] a) (𝓝 l)) ∧
      ((𝓝[I ∩ Ioi a] a).NeBot → ∃ l : ℝ, Tendsto f (𝓝[I ∩ Ioi a] a) (𝓝 l))

/-- Definition 5: `φ` is a Pólya frequency function of order `n` (`PF_n`) if
(a) `0 < ∫ φ < ∞` and (b) `det [φ(x_i - t_j)]_{1,k} ≥ 0` whenever `1 ≤ k ≤ n`,
`x₁ < ⋯ < x_k` and `t₁ < ⋯ < t_k`. Condition (b) with `k = 1` forces `φ ≥ 0`, so (a) is
Lebesgue integrability together with a positive integral. -/
def IsPF (n : ℕ) (φ : ℝ → ℝ) : Prop :=
  (Integrable φ ∧ 0 < ∫ x, φ x) ∧
    ∀ k : ℕ, 1 ≤ k → k ≤ n → ∀ x t : Fin k → ℝ, StrictMono x → StrictMono t →
      0 ≤ (Matrix.of fun i j : Fin k => φ (x i - t j)).det

/-- Definition 6: `φ` is a Pólya frequency function (`PFF`) if it is `PF_n` for all `n ≥ 1`. -/
def IsPFF (φ : ℝ → ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → IsPF n φ

/-- Definition 7: a `PFF` function with total integral `1` is a Pólya density. -/
def IsPolyaDensity (φ : ℝ → ℝ) : Prop :=
  IsPFF φ ∧ ∫ x, φ x = 1

/-- Definition 8: a Pólya density vanishing on `R⁻ = (-∞, 0)` is a one-sided Pólya density. -/
def IsOneSidedPolyaDensity (φ : ℝ → ℝ) : Prop :=
  IsPolyaDensity φ ∧ ∀ x : ℝ, x < 0 → φ x = 0

/-- §III / §VIII: `f` is PF-integrable if the convolution `f * ψ` exists (the integral is finite)
at every point whenever `ψ` is a Pólya frequency function. -/
def PFIntegrable (f : ℝ → ℝ) : Prop :=
  ∀ ψ : ℝ → ℝ, IsPFF ψ → ∀ y : ℝ, Integrable (fun ξ => f (y - ξ) * ψ ξ)

/-- Definition 1: `f` is non-`K`-decreasing on `X` if `f x ≤ f y + K` for `x, y ∈ X`, `x ≤ y`. -/
def NonKDecreasingOn (f : ℝ → ℝ) (K : ℝ) (X : Set ℝ) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, x ≤ y → f x ≤ f y + K

/-- Definition 2: the class `C_a(K)` (for `K ≥ 0`, `a ∈ ℝ`): functions `f` which, for some
`I ∈ {(-∞, a), (-∞, a]}`, are (i) piecewise continuous, (ii) PF-integrable, (iii) nonincreasing
on `I`, (iv) non-`K`-decreasing on `ℝ \ I`, and (v) satisfy `f x → ∞` as `|x| → ∞`. -/
def CaK (a K : ℝ) (f : ℝ → ℝ) : Prop :=
  0 ≤ K ∧ ∃ I : Set ℝ, (I = Iio a ∨ I = Iic a) ∧
    PiecewiseContinuousOn f univ ∧ PFIntegrable f ∧ AntitoneOn f I ∧
    NonKDecreasingOn f K Iᶜ ∧ Tendsto f (cocompact ℝ) atTop

/-- Definition 3: the class `C(K)` (for `K ≥ 0`): continuous functions lying in `C_a(K)` for
some `a ∈ ℝ`. -/
def CK (K : ℝ) (f : ℝ → ℝ) : Prop :=
  0 ≤ K ∧ Continuous f ∧ ∃ a : ℝ, CaK a K f

/-- Definition 10: `f` is quasi-`K`-convex on the convex set `X` if `x, y ∈ X`, `x ≤ y` and
`0 ≤ λ ≤ 1` imply `f(λx + (1-λ)y) ≤ max (f x) (f y + K)`  (27). -/
def QuasiKConvexOn (f : ℝ → ℝ) (K : ℝ) (X : Set ℝ) : Prop :=
  Convex ℝ X ∧ ∀ x ∈ X, ∀ y ∈ X, x ≤ y → ∀ l : ℝ, 0 ≤ l → l ≤ 1 →
    f (l * x + (1 - l) * y) ≤ max (f x) (f y + K)

/-- Definition 4: an ordering policy function `y` (post-order inventory level as a function of the
pre-order level) is a generalized `(s, S)` policy if (i) `y x = x` for `s ≤ x` and
(ii) `y z ≥ y x ≥ S ≥ s` for `z < x < s`. -/
def IsGenSS (y : ℝ → ℝ) (s S : ℝ) : Prop :=
  (∀ x : ℝ, s ≤ x → y x = x) ∧
    (∀ z x : ℝ, z < x → x < s → y x ≤ y z ∧ S ≤ y x) ∧ s ≤ S

/-- The (negative) exponential density with parameter `lam`:
`lam * exp (-lam * t)` for `t ≥ 0` and `0` otherwise. -/
noncomputable def expDensity (lam : ℝ) (t : ℝ) : ℝ :=
  if 0 ≤ t then lam * Real.exp (-lam * t) else 0

end PorteusSS
