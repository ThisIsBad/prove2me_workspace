import Mathlib

namespace RobustGeneralization.BernLower

open scoped BigOperators

/-- The ambient space `ℝ^d` with the Euclidean inner product. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Labels `y ∈ {±1}` are encoded as `Bool`: `true ↦ +1`, `false ↦ -1`. -/
def lab (b : Bool) : ℝ := if b then 1 else -1

/-- The ℓ∞ ball `B∞^ε(x) = {x' ∈ ℝ^d | ‖x' - x‖∞ ≤ ε}`, written coordinatewise. -/
def linfBall {d : ℕ} (x : E d) (ε : ℝ) : Set (E d) :=
  {x' | ∀ i, |x' i - x i| ≤ ε}

/-- The linear classifier `f_w(x) = sgn ⟨w, x⟩`, with the tie `⟨w, x⟩ = 0` sent to `+1`. -/
noncomputable def linClf {d : ℕ} (w : E d) (x : E d) : Bool :=
  decide (0 ≤ inner ℝ w x)

/-- The hypercube point `x ∈ {±1}^d ⊂ ℝ^d` encoded by a sign vector `s : Fin d → Bool`. -/
noncomputable def pm {d : ℕ} (s : Fin d → Bool) : E d :=
  WithLp.toLp 2 (fun i => lab (s i))

/-- Probability of one sample `(x, y) = (pm s, y)` under the `(θ, τ)`-Bernoulli model
(Definition 7): `y` uniform on `{±1}`, then independently for each coordinate
`x_i = y θ_i` with probability `1/2 + τ` and `x_i = -y θ_i` with probability `1/2 - τ`.
The condition `s i = (y == θ i)` says exactly `x_i = y θ_i`. -/
noncomputable def bernW {d : ℕ} (θ : Fin d → Bool) (τ : ℝ) (p : (Fin d → Bool) × Bool) : ℝ :=
  (1 / 2) * ∏ i, (if p.1 i = (p.2 == θ i) then 1 / 2 + τ else 1 / 2 - τ)

/-- The `ℓ∞^ε`-robust classification error (Definition 3) of a classifier `f : ℝ^d → {±1}`
under the `(θ, τ)`-Bernoulli model: the probability that some `x' ∈ B∞^ε(x)` has `f x' ≠ y`. -/
noncomputable def robErr {d : ℕ} (θ : Fin d → Bool) (τ : ℝ) (f : E d → Bool) (ε : ℝ) : ℝ := by
  classical
  exact ∑ p : (Fin d → Bool) × Bool,
    bernW θ τ p * (if ∃ x' ∈ linfBall (pm p.1) ε, f x' ≠ p.2 then 1 else 0)

/-- Joint weight of `(θ⋆, S)` when `θ⋆` is uniform on `{±1}^d` and `S` consists of `n`
independent samples from the `(θ⋆, τ)`-Bernoulli model. -/
noncomputable def joint {d n : ℕ} (τ : ℝ) (θ : Fin d → Bool)
    (S : Fin n → (Fin d → Bool) × Bool) : ℝ :=
  (1 / 2) ^ d * ∏ k, bernW θ τ (S k)

/-- Expected `ℓ∞^ε`-robust classification error of the linear classifier `f_w`, `w = g S`,
output by a linear-classifier learning algorithm `g` on `n` samples, when `θ⋆` is uniform on
`{±1}^d` and the samples are drawn from the `(θ⋆, τ)`-Bernoulli model. -/
noncomputable def expRobErr {d n : ℕ} (g : (Fin n → (Fin d → Bool) × Bool) → E d)
    (τ ε : ℝ) : ℝ :=
  ∑ θ : Fin d → Bool, ∑ S : Fin n → (Fin d → Bool) × Bool,
    joint τ θ S * robErr θ τ (linClf (g S)) ε

/-- Posterior probability `Pr[θ⋆_i = b | S]` (Bayes' rule as a ratio of joint weights). -/
noncomputable def postProb {d n : ℕ} (τ : ℝ) (S : Fin n → (Fin d → Bool) × Bool)
    (i : Fin d) (b : Bool) : ℝ := by
  classical
  exact (∑ θ : Fin d → Bool, if θ i = b then joint τ θ S else 0) /
    (∑ θ : Fin d → Bool, joint τ θ S)

/-- Posterior mean `E[θ⋆_i | S] = Pr[θ⋆_i = +1 | S] - Pr[θ⋆_i = -1 | S]`. -/
noncomputable def postMean {d n : ℕ} (τ : ℝ) (S : Fin n → (Fin d → Bool) × Bool)
    (i : Fin d) : ℝ :=
  postProb τ S i true - postProb τ S i false

/-- One-dimensional `(θ, τ)`-Bernoulli model (`d = 1`, as in Lemma 29): probability of one
sample `(x, y) ∈ {±1} × {±1}`, `x = y θ` with probability `1/2 + τ`. -/
noncomputable def bern1W (θ : Bool) (τ : ℝ) (p : Bool × Bool) : ℝ :=
  (1 / 2) * (if p.1 = (p.2 == θ) then 1 / 2 + τ else 1 / 2 - τ)

/-- Joint weight of `(θ, S)` in the one-dimensional model, `θ` uniform on `{±1}`. -/
noncomputable def joint1 {n : ℕ} (τ : ℝ) (θ : Bool) (S : Fin n → Bool × Bool) : ℝ :=
  (1 / 2) * ∏ k, bern1W θ τ (S k)

/-- Posterior `Pr[θ = b | S]` in the one-dimensional model. -/
noncomputable def post1 {n : ℕ} (τ : ℝ) (S : Fin n → Bool × Bool) (b : Bool) : ℝ :=
  joint1 τ b S / (∑ θ : Bool, joint1 τ θ S)

/-- Posterior odds `Pr[θ = +1 | S] / Pr[θ = -1 | S]` in the one-dimensional model. -/
noncomputable def odds1 {n : ℕ} (τ : ℝ) (S : Fin n → Bool × Bool) : ℝ :=
  post1 τ S true / post1 τ S false

/-- A product law on `{±1}^d` whose `i`-th coordinate has mean `m i`
(requires `|m i| ≤ 1` to be a probability law). -/
noncomputable def prodLaw {d : ℕ} (m : Fin d → ℝ) (θ : Fin d → Bool) : ℝ :=
  ∏ i, (1 + m i * lab (θ i)) / 2

end RobustGeneralization.BernLower
