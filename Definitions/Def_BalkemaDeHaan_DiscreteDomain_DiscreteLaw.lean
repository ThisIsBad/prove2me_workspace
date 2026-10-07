import Mathlib

open MeasureTheory Filter Topology

namespace BalkemaDeHaan.DiscreteDomain

/-- `ν` is a discrete law whose discontinuity points form the unbounded increasing sequence
`t₀ < t₁ < t₂ < ⋯` (§3, pp. 799–800, PDF 8–9): `t` is strictly increasing and tends to `∞`,
every `t n` carries positive mass, and `ν` puts no mass off `{t₀, t₁, …}`. Its distribution
function `cdf ν` is then a right-continuous step function jumping exactly at the `t n`. -/
def IsDiscreteWithJumps (ν : Measure ℝ) (t : ℕ → ℝ) : Prop :=
  StrictMono t ∧ Tendsto t atTop atTop ∧ ν (Set.range t)ᶜ = 0 ∧ ∀ n, 0 < ν {t n}

/-- Condition (12a), p. 800 (PDF 9): `(t_{n+1} - t_n)/(t_n - t_{n-1}) → e^{pc}` as `n → ∞`
(indexed from `n = 1`). -/
def GapRatio (t : ℕ → ℝ) (p c : ℝ) : Prop :=
  Tendsto (fun n : ℕ => (t (n + 2) - t (n + 1)) / (t (n + 1) - t n)) atTop
    (𝓝 (Real.exp (p * c)))

/-- Condition (12b), p. 800 (PDF 9): `R(t_{n+1})/R(t_n) → e^{-p}` as `n → ∞`, where
`R(x) = ν((x, ∞))` is the BalkemaDeHaan.LimitTypes.tail of `ν`. -/
def TailRatio (ν : Measure ℝ) (t : ℕ → ℝ) (p : ℝ) : Prop :=
  Tendsto (fun n : ℕ => (ν (Set.Ioi (t (n + 1)))).toReal / (ν (Set.Ioi (t n))).toReal) atTop
    (𝓝 (Real.exp (-p)))

/-- Tail equivalence (p. 800, PDF 9): two laws whose distribution functions satisfy
`F_i(x) < 1` for all `x` are BalkemaDeHaan.LimitTypes.tail equivalent if `1 - F₁(x) ~ 1 - F₂(x)` as `x → ∞`. -/
def TailEquiv (μ₁ μ₂ : Measure ℝ) : Prop :=
  (∀ x, 0 < μ₁ (Set.Ioi x)) ∧ (∀ x, 0 < μ₂ (Set.Ioi x)) ∧
  Tendsto (fun x => (μ₁ (Set.Ioi x)).toReal / (μ₂ (Set.Ioi x)).toReal) atTop (𝓝 1)

end BalkemaDeHaan.DiscreteDomain
