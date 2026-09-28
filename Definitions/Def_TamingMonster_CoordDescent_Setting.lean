import Mathlib

namespace TamingMonster.CoordDescent

variable {X : Type*} {K t : ℕ}

/-- A history `H_t` of `t` interaction records `(x_i, a_i, r_i(a_i), p_i(a_i))`, `i = 1, …, t`
(§2.1, p. 3), indexed here by `Fin t`: the context, the chosen action in `A = Fin K`, the observed
reward `r_i(a_i) ∈ [0,1]`, and the probability `p_i(a_i) ∈ (0,1]` with which the action was
chosen. (The paper writes `p ∈ [0,1]`; a taken action has positive probability, and Eq. (1)
divides by it.) -/
structure History (X : Type*) (K t : ℕ) where
  x : Fin t → X
  a : Fin t → Fin K
  r : Fin t → ℝ
  p : Fin t → ℝ
  r_mem : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1
  p_mem : ∀ i, p i ∈ Set.Ioc (0 : ℝ) 1

/-- The empirical expectation `Ê_{x∼H_t}[f(x)] = (1/t) ∑_{i=1}^t f(x_i)`: a context drawn
uniformly from the `t` contexts of the history (§2.1). -/
noncomputable def empExp (H : History X K t) (f : X → ℝ) : ℝ :=
  (1 / (t : ℝ)) * ∑ i, f (H.x i)

/-- The inverse propensity scoring estimate, Eq. (1):
`R̂_t(π) = (1/t) ∑_{i=1}^t r_i(a_i) 1{π(x_i) = a_i} / p_i(a_i)`. -/
noncomputable def ipsEstimate (H : History X K t) (π : X → Fin K) : ℝ :=
  (1 / (t : ℝ)) * ∑ i, H.r i * (if π (H.x i) = H.a i then (1 : ℝ) else 0) / H.p i

/-- The estimated regret `R̂eg_t(π) = R̂_t(π_t) − R̂_t(π)` with `π_t ∈ argmax_{π' ∈ Π} R̂_t(π')`
(§2.2), written as `max_{π' ∈ Π} R̂_t(π') − R̂_t(π)` (the maximum over the finite class `Π`). -/
noncomputable def estRegret (Pi : Finset (X → Fin K)) (H : History X K t) (π : X → Fin K) : ℝ :=
  (⨆ π' : Pi, ipsEstimate H (π' : X → Fin K)) - ipsEstimate H π

/-- `b_π = R̂eg_t(π) / (ψ μ)` with `ψ = 100` ((OP), p. 5). -/
noncomputable def bCoef (Pi : Finset (X → Fin K)) (H : History X K t) (μ : ℝ)
    (π : X → Fin K) : ℝ :=
  estRegret Pi H π / (100 * μ)

/-- The smoothed projection of the (unnormalized) weights `Q` (§2.4):
`Q^μ(a | x) = (1 − Kμ) ∑_{π ∈ Π : π(x) = a} Q(π) + μ`. -/
noncomputable def smoothedProj (Pi : Finset (X → Fin K)) (μ : ℝ) (Q : Pi → ℝ) (x : X)
    (a : Fin K) : ℝ :=
  (1 - (K : ℝ) * μ) * (∑ π ∈ Finset.univ.filter (fun π : Pi => (π : X → Fin K) x = a), Q π) + μ

/-- `Q ∈ Δ^Π = {Q ∈ ℝ^Π : Q(π) ≥ 0 ∀ π ∈ Π, ∑_{π ∈ Π} Q(π) ≤ 1}` (§2.1). -/
def InSimplex (Pi : Finset (X → Fin K)) (Q : Pi → ℝ) : Prop :=
  (∀ π, 0 ≤ Q π) ∧ ∑ π, Q π ≤ 1

/-- `Q` is a solution to the optimization problem (OP) (p. 5) for history `H_t` and minimum
probability `μ`: `Q ∈ Δ^Π`,
(2) `∑_{π ∈ Π} Q(π) b_π ≤ 2K`, and
(3) `∀ π ∈ Π, Ê_{x∼H_t}[1 / Q^μ(π(x) | x)] ≤ 2K + b_π`. -/
def SolvesOP (Pi : Finset (X → Fin K)) (H : History X K t) (μ : ℝ) (Q : Pi → ℝ) : Prop :=
  InSimplex Pi Q ∧
  ∑ π, Q π * bCoef Pi H μ (π : X → Fin K) ≤ 2 * (K : ℝ) ∧
  ∀ π : Pi, empExp H (fun x => 1 / smoothedProj Pi μ Q x ((π : X → Fin K) x))
      ≤ 2 * (K : ℝ) + bCoef Pi H μ (π : X → Fin K)

end TamingMonster.CoordDescent
