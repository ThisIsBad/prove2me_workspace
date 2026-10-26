import Mathlib

namespace NelderMeadLD.Conv1D

/-- The parameter conditions (2.1) of Lagarias–Reeds–Wright–Wright (p. 115):
`ρ > 0`, `χ > 1`, `χ > ρ`, `0 < γ < 1`, `0 < σ < 1`. -/
def ParamsOK (ρ χ γ σ : ℝ) : Prop :=
  0 < ρ ∧ 1 < χ ∧ ρ < χ ∧ 0 < γ ∧ γ < 1 ∧ 0 < σ ∧ σ < 1

/-! The state of the one-dimensional method is the ordered pair `p = (x₁, x₂)`:
`p.1` is the best vertex `x₁` and `p.2` the worst vertex `x₂`. In dimension 1 the
centroid `x̄` of the `n = 1` best points is `x₁`. -/

/-- Reflection point (2.4) with `n = 1`: `x_r = x₁ + ρ (x₁ − x₂)`. -/
def xr (ρ : ℝ) (p : ℝ × ℝ) : ℝ := p.1 + ρ * (p.1 - p.2)

/-- Expansion point (2.5) with `n = 1`: `x_e = x₁ + ρχ (x₁ − x₂)`. -/
def xe (ρ χ : ℝ) (p : ℝ × ℝ) : ℝ := p.1 + ρ * χ * (p.1 - p.2)

/-- Outside contraction point (2.6) with `n = 1`: `x_c = x₁ + ργ (x₁ − x₂)`. -/
def xc (ρ γ : ℝ) (p : ℝ × ℝ) : ℝ := p.1 + ρ * γ * (p.1 - p.2)

/-- Inside contraction point (2.7) with `n = 1`: `x_cc = x₁ − γ (x₁ − x₂)`. -/
def xcc (γ : ℝ) (p : ℝ × ℝ) : ℝ := p.1 - γ * (p.1 - p.2)

/-- Shrink point of step 5 with `n = 1`: `v₂ = x₁ + σ (x₂ − x₁)`. -/
def xsh (σ : ℝ) (p : ℝ × ℝ) : ℝ := p.1 + σ * (p.2 - p.1)

/-- The kind of a Nelder–Mead iteration. -/
inductive Move
  | reflect
  | expand
  | outside
  | inside
  | shrink
  deriving DecidableEq

/-- The case analysis of steps 2–5 of Algorithm NM (pp. 115–116) for `n = 1`, where
`f_n = f₁` so step 2 never terminates the iteration:
* `f_r < f₁`: expand; accept `x_e` if `f_e < f_r`, otherwise accept `x_r`;
* `f₁ ≤ f_r < f₂`: outside contraction, accepted iff `f_c ≤ f_r`, otherwise shrink;
* `f_r ≥ f₂`: inside contraction, accepted iff `f_cc < f₂`, otherwise shrink. -/
noncomputable def move (f : ℝ → ℝ) (ρ χ γ : ℝ) (p : ℝ × ℝ) : Move :=
  if f (xr ρ p) < f p.1 then
    (if f (xe ρ χ p) < f (xr ρ p) then Move.expand else Move.reflect)
  else if f (xr ρ p) < f p.2 then
    (if f (xc ρ γ p) ≤ f (xr ρ p) then Move.outside else Move.shrink)
  else
    (if f (xcc γ p) < f p.2 then Move.inside else Move.shrink)

/-- The point accepted at an iteration of the given kind (for a shrink, the new vertex `v₂`). -/
def acceptedPoint (ρ χ γ σ : ℝ) (p : ℝ × ℝ) : Move → ℝ
  | Move.reflect => xr ρ p
  | Move.expand => xe ρ χ p
  | Move.outside => xc ρ γ p
  | Move.inside => xcc γ p
  | Move.shrink => xsh σ p

/-- The ordering rule for `n = 1` (pp. 116–117): the retained vertex `x₁` and the new point
`v` form the next pair; `v` becomes the best vertex iff `f v < f x₁`, otherwise it is placed
second (ties give the new point the highest index). For a shrink this is also the paper's
shrink ordering rule (`x₁` stays first when `f v₂ = f x₁`). -/
noncomputable def place (f : ℝ → ℝ) (x1 v : ℝ) : ℝ × ℝ :=
  if f v < f x1 then (v, x1) else (x1, v)

/-- One iteration of Algorithm NM in dimension 1. -/
noncomputable def step (f : ℝ → ℝ) (ρ χ γ σ : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  place f p.1 (acceptedPoint ρ χ γ σ p (move f ρ χ γ p))

/-- The Nelder–Mead run from the initial ordered pair `p0`: `run … k = Δ_k`. -/
noncomputable def run (f : ℝ → ℝ) (ρ χ γ σ : ℝ) (p0 : ℝ × ℝ) : ℕ → ℝ × ℝ :=
  fun k => (step f ρ χ γ σ)^[k] p0

/-- A nondegenerate initial interval, ordered as in (2.3): `x₁ ≠ x₂` and `f(x₁) ≤ f(x₂)`. -/
def IsStart (f : ℝ → ℝ) (p0 : ℝ × ℝ) : Prop :=
  p0.1 ≠ p0.2 ∧ f p0.1 ≤ f p0.2

/-- The diameter of the one-dimensional simplex: `diam(Δ) = |x₁ − x₂|`. -/
def diam (p : ℝ × ℝ) : ℝ := |p.1 - p.2|

/-- The constant (4.3): `N_NM = max(1/(ργ), ρ/γ, ρχ, χ − 1)`. -/
noncomputable def NNM (ρ χ γ : ℝ) : ℝ :=
  max (max (1 / (ρ * γ)) (ρ / γ)) (max (ρ * χ) (χ - 1))

/-- `int(a, b]`: the interval with endpoints `a` and `b`, open at `a` and closed at `b`,
regardless of whether `a < b` or `a > b` (p. 124). Like `(a, a]`, it is empty when `a = b`. -/
def inIoc' (a b x : ℝ) : Prop :=
  (min a b < x ∧ x < max a b) ∨ (x = b ∧ a ≠ b)

/-- The proximity property (4.4): `x_min ∈ int(x₂, x₁ + N_NM (x₁ − x₂)]`. -/
noncomputable def Proximity (ρ χ γ xmin : ℝ) (p : ℝ × ℝ) : Prop :=
  inIoc' p.2 (p.1 + NNM ρ χ γ * (p.1 - p.2)) xmin

/-- The "up–down–up" condition of (4.2): `f₂ ≥ f₁` and `f₁ ≤ f_e`. -/
def Bracketed (ρ χ : ℝ) (f : ℝ → ℝ) (p : ℝ × ℝ) : Prop :=
  f p.1 ≤ f p.2 ∧ f p.1 ≤ f (xe ρ χ p)

end NelderMeadLD.Conv1D
