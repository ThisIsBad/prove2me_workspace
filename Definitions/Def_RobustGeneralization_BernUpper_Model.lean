import Mathlib

namespace RobustGeneralization.BernUpper

/-- The ambient space `ℝ^d` with its Euclidean (ℓ2) norm and inner product. -/
abbrev E (d : ℕ) : Type := EuclideanSpace ℝ (Fin d)

/-- Labels `y ∈ {±1}` are encoded as `Bool`: `true ↦ +1`, `false ↦ -1`. -/
noncomputable def lab (b : Bool) : ℝ := if b then 1 else -1

/-- The sign vector in `{±1}^d ⊆ ℝ^d` with coordinates `lab (s i)`. -/
noncomputable def pm {d : ℕ} (s : Fin d → Bool) : E d := WithLp.toLp 2 (fun i => lab (s i))

/-- The ℓ∞ ball `B∞^ε(x) = {x' ∈ ℝ^d | ‖x' − x‖∞ ≤ ε}`, written coordinatewise
(Schmidt et al., arXiv:1804.11285v2, p. 5, Definition 3). -/
def linfBall {d : ℕ} (x : E d) (ε : ℝ) : Set (E d) := {x' : E d | ∀ i, |x' i - x i| ≤ ε}

/-- The linear classifier `f_w(x) = sgn(⟨w, x⟩)` (p. 5), with the tie `⟨w, x⟩ = 0` sent to `+1`
(`true`). -/
noncomputable def linClf {d : ℕ} (w : E d) (x : E d) : Bool := decide (0 ≤ inner ℝ w x)

/-- Probability weight of one sample `(x, y) = (pm s, y)` under the `(θ⋆, τ)`-Bernoulli model
(Definition 7, pp. 6–7), with `θ⋆ = pm θ`: the label is uniform on `{±1}` and, given `y`, the
coordinates are independent with `x_i = y θ⋆_i` with probability `1/2 + τ` and `x_i = −y θ⋆_i`
with probability `1/2 − τ`. -/
noncomputable def bernW {d : ℕ} (θ : Fin d → Bool) (τ : ℝ) (p : (Fin d → Bool) × Bool) : ℝ :=
  (1 / 2) * ∏ i, (if p.1 i = (p.2 == θ i) then 1 / 2 + τ else 1 / 2 - τ)

open Classical in
/-- The probability, for one sample `p = (s, y)` drawn from the `(θ⋆, τ)`-Bernoulli model, of the
event `A`. -/
noncomputable def bprob {d : ℕ} (θ : Fin d → Bool) (τ : ℝ)
    (A : (Fin d → Bool) × Bool → Prop) : ℝ :=
  ∑ p, bernW θ τ p * (if A p then 1 else 0)

/-- Classification error `P[f(x) ≠ y]` of a classifier `f : ℝ^d → {±1}` (Definition 2, p. 5). -/
noncomputable def clsErr {d : ℕ} (θ : Fin d → Bool) (τ : ℝ) (f : E d → Bool) : ℝ :=
  bprob θ τ (fun p => f (pm p.1) ≠ p.2)

/-- ℓ∞^ε-robust classification error `P[∃ x' ∈ B∞^ε(x) : f(x') ≠ y]` (Definition 3, p. 5). -/
noncomputable def robErr {d : ℕ} (θ : Fin d → Bool) (τ : ℝ) (f : E d → Bool) (ε : ℝ) : ℝ :=
  bprob θ τ (fun p => ∃ x' ∈ linfBall (pm p.1) ε, f x' ≠ p.2)

/-- The thresholding map `T : ℝ^d → ℝ^d`, `T(x)_i = +1` if `x_i ≥ 0` and `−1` otherwise (p. 7). -/
noncomputable def thr {d : ℕ} (x : E d) : E d := WithLp.toLp 2 (fun i => if 0 ≤ x i then (1 : ℝ) else -1)

/-- The classifier `f_w ∘ T`. -/
noncomputable def thrClf {d : ℕ} (w : E d) (x : E d) : Bool := linClf w (thr x)

/-- The vector `z = yx` built from one sample `p = (s, y)`. -/
noncomputable def zvec {d : ℕ} (p : (Fin d → Bool) × Bool) : E d := lab p.2 • pm p.1

/-- The unit vector `ŵ = z / ‖z‖₂` in the direction of `z = yx` (`0` when `d = 0`). -/
noncomputable def unitZ {d : ℕ} (p : (Fin d → Bool) × Bool) : E d := ‖zvec p‖⁻¹ • zvec p

end RobustGeneralization.BernUpper
