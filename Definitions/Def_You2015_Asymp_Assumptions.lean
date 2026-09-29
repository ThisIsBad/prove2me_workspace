import Mathlib

open scoped NNReal

namespace You2015.Asymp

variable {n m N : ℕ}

/-- **Assumption 2.1.** `K₁, K₂ > 0`; the coefficients `f` and `g` are locally Lipschitz
continuous in `x`, uniformly in `(i, t)` (for every `R` there is `L ≥ 0` with
`|f(x,i,t) − f(y,i,t)| ≤ L|x − y|` and `|g(x,i,t) − g(y,i,t)| ≤ L|x − y|` whenever
`|x|, |y| ≤ R`); and the linear growth condition (2.4) `|f(x,i,t)| ≤ K₁|x|`,
`|g(x,i,t)| ≤ K₂|x|` holds. `|g|` is the trace (Frobenius) norm of the `n × m` matrix whose
columns are `g x i t k`, so its square is `∑ₖ |g x i t k|²`. -/
def Assumption21
    (f : EuclideanSpace ℝ (Fin n) → Fin N → ℝ≥0 → EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n) → Fin N → ℝ≥0 → Fin m → EuclideanSpace ℝ (Fin n))
    (K₁ K₂ : ℝ) : Prop :=
  0 < K₁ ∧ 0 < K₂ ∧
    (∀ R : ℝ, ∃ L : ℝ, 0 ≤ L ∧ ∀ x y i t, ‖x‖ ≤ R → ‖y‖ ≤ R →
      ‖f x i t - f y i t‖ ≤ L * ‖x - y‖ ∧
        ∑ k, ‖g x i t k - g y i t k‖ ^ 2 ≤ (L * ‖x - y‖) ^ 2) ∧
    ∀ x i t, ‖f x i t‖ ≤ K₁ * ‖x‖ ∧ ∑ k, ‖g x i t k‖ ^ 2 ≤ K₂ ^ 2 * ‖x‖ ^ 2

/-- **Assumption 2.2.** `K₃ > 0`, the controller is globally Lipschitz,
`|u(x,i,t) − u(y,i,t)| ≤ K₃|x − y|` (2.6), and `u(0,i,t) = 0` (2.7). -/
def Assumption22
    (u : EuclideanSpace ℝ (Fin n) → Fin N → ℝ≥0 → EuclideanSpace ℝ (Fin n)) (K₃ : ℝ) : Prop :=
  0 < K₃ ∧ (∀ x y i t, ‖u x i t - u y i t‖ ≤ K₃ * ‖x - y‖) ∧ ∀ i t, u 0 i t = 0

/-- The class `C^{2,1}(Rⁿ × S × R₊; R₊)`, with its derivatives given as witnesses tied to `U`:
`U ≥ 0`; `Ux x i t` is the Fréchet derivative of `U(·, i, t)` at `x` and `Uxx x i t` that of
`Ux(·, i, t)` at `x`; `Ut x i t` is the (one-sided at `t = 0`) derivative of `s ↦ U(x, i, s)`
on `[0, ∞)` at `t`; and `U, Ut, Ux, Uxx` are jointly continuous in `(x, t)` for each mode `i`. -/
structure C21
    (U Ut : EuclideanSpace ℝ (Fin n) → Fin N → ℝ≥0 → ℝ)
    (Ux : EuclideanSpace ℝ (Fin n) → Fin N → ℝ≥0 → (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
    (Uxx : EuclideanSpace ℝ (Fin n) → Fin N → ℝ≥0 →
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) : Prop where
  nonneg : ∀ x i t, 0 ≤ U x i t
  hasFDerivAt_x : ∀ x i t, HasFDerivAt (fun y => U y i t) (Ux x i t) x
  hasFDerivAt_xx : ∀ x i t, HasFDerivAt (fun y => Ux y i t) (Uxx x i t) x
  hasDerivWithinAt_t : ∀ x i t,
    HasDerivWithinAt (fun s : ℝ => U x i s.toNNReal) (Ut x i t) (Set.Ici 0) (t : ℝ)
  cont_U : ∀ i, Continuous (fun p : EuclideanSpace ℝ (Fin n) × ℝ≥0 => U p.1 i p.2)
  cont_Ut : ∀ i, Continuous (fun p : EuclideanSpace ℝ (Fin n) × ℝ≥0 => Ut p.1 i p.2)
  cont_Ux : ∀ i, Continuous (fun p : EuclideanSpace ℝ (Fin n) × ℝ≥0 => Ux p.1 i p.2)
  cont_Uxx : ∀ i, Continuous (fun p : EuclideanSpace ℝ (Fin n) × ℝ≥0 => Uxx p.1 i p.2)

/-- The operator (3.2), with the continuous-time feedback `u(x, i, t)`:
`𝓛U(x,i,t) = U_t + U_x[f + u] + ½ trace[gᵀ U_xx g] + ∑ⱼ γ_ij U(x, j, t)`, where
`trace[gᵀ U_xx g] = ∑ₖ U_xx(g_k, g_k)` over the columns `g_k` of `g`. -/
noncomputable def LU (Γ : Matrix (Fin N) (Fin N) ℝ)
    (f u : EuclideanSpace ℝ (Fin n) → Fin N → ℝ≥0 → EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n) → Fin N → ℝ≥0 → Fin m → EuclideanSpace ℝ (Fin n))
    (U Ut : EuclideanSpace ℝ (Fin n) → Fin N → ℝ≥0 → ℝ)
    (Ux : EuclideanSpace ℝ (Fin n) → Fin N → ℝ≥0 → (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
    (Uxx : EuclideanSpace ℝ (Fin n) → Fin N → ℝ≥0 →
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin N) (t : ℝ≥0) : ℝ :=
  Ut x i t + Ux x i t (f x i t + u x i t)
    + (1 / 2) * ∑ k, Uxx x i t (g x i t k) (g x i t k)
    + ∑ j, Γ i j * U x j t

/-- **Assumption 3.1** for the given `U` (with derivatives `Ut, Ux, Uxx`) and numbers
`lam₁ = λ₁`, `lam₂ = λ₂`: `λ₁, λ₂ > 0` and (3.3)
`𝓛U(x,i,t) + λ₁|U_x(x,i,t)|² ≤ −λ₂|x|²` for all `(x, i, t)`. The norm of `Ux x i t` is the
operator norm of a linear functional on Euclidean space, i.e. the Euclidean norm of the
gradient. -/
def Assumption31 (Γ : Matrix (Fin N) (Fin N) ℝ)
    (f u : EuclideanSpace ℝ (Fin n) → Fin N → ℝ≥0 → EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n) → Fin N → ℝ≥0 → Fin m → EuclideanSpace ℝ (Fin n))
    (U Ut : EuclideanSpace ℝ (Fin n) → Fin N → ℝ≥0 → ℝ)
    (Ux : EuclideanSpace ℝ (Fin n) → Fin N → ℝ≥0 → (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
    (Uxx : EuclideanSpace ℝ (Fin n) → Fin N → ℝ≥0 →
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
    (lam₁ lam₂ : ℝ) : Prop :=
  0 < lam₁ ∧ 0 < lam₂ ∧
    ∀ x i t, LU Γ f u g U Ut Ux Uxx x i t + lam₁ * ‖Ux x i t‖ ^ 2 ≤ -lam₂ * ‖x‖ ^ 2

/-- **Condition (3.5)** on the observation interval `τ`: `τ > 0`,
`λ₂ > (τK₃²/λ₁)[2τ(K₁² + 2K₃²) + K₂²]` and `τ ≤ 1/(4K₃)`. -/
def Condition35 (K₁ K₂ K₃ lam₁ lam₂ : ℝ) (τ : ℝ≥0) : Prop :=
  0 < τ ∧
    (τ : ℝ) * K₃ ^ 2 / lam₁ * (2 * τ * (K₁ ^ 2 + 2 * K₃ ^ 2) + K₂ ^ 2) < lam₂ ∧
    (τ : ℝ) ≤ 1 / (4 * K₃)

end You2015.Asymp
