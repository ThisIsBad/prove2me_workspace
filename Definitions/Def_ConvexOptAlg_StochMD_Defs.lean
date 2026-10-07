import Mathlib

namespace ConvexOptAlg.StochMD

open MeasureTheory Filter Topology

/-- The Bregman divergence (Bubeck, arXiv:1405.4980v2, Ch. 4 preamble, p. 297):
`D_Φ(x, y) = Φ(x) − Φ(y) − ∇Φ(y)⊤(x − y)`. The gradient `∇Φ(y)` is the continuous linear functional
`Φ' y : E →L[ℝ] ℝ`, and `∇Φ(y)⊤v` is its value `Φ' y v`. -/
def bregman {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Φ : E → ℝ) (Φ' : E → E →L[ℝ] ℝ) (x y : E) : ℝ :=
  Φ x - Φ y - Φ' y (x - y)

/-- `Φ` is a mirror map on the convex open set `D` with gradient map `Φ'` (§4.1, p. 298):
`D` is open and convex, and
(i) `Φ` is strictly convex on `D` and differentiable at every point of `D`, with derivative `Φ' x`;
(ii) the gradient takes all possible values, `∇Φ(D) = (ℝⁿ)*`: every continuous linear functional
is `Φ' y` for some `y ∈ D`;
(iii) the gradient diverges on the boundary of `D`: for every `z ∈ ∂D`, `‖∇Φ(x)‖ → +∞` as `x → z`
inside `D` (the norm of `∇Φ(x)` is the dual, i.e. operator, norm).
The set conditions `X ⊆ closure D` and `X ∩ D ≠ ∅` of §4.1 are separate hypotheses of each theorem. -/
def IsMirrorMap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : Set E) (Φ : E → ℝ) (Φ' : E → E →L[ℝ] ℝ) : Prop :=
  IsOpen D ∧ Convex ℝ D ∧ StrictConvexOn ℝ D Φ ∧
    (∀ x ∈ D, HasFDerivAt Φ (Φ' x) x) ∧
    (∀ φ : E →L[ℝ] ℝ, ∃ y ∈ D, Φ' y = φ) ∧
    (∀ z ∈ frontier D, Tendsto (fun x => ‖Φ' x‖) (𝓝[D] z) atTop)

/-- `Φ` is `ρ`-strongly convex on the set `S` w.r.t. `‖·‖`, with gradient map `Φ'`
(Ch. 4 preamble (iii), p. 297, for a differentiable function, whose only subgradient is its
gradient): `Φ(x) − Φ(y) ≤ ∇Φ(x)⊤(x − y) − (ρ/2)‖x − y‖²` for all `x, y ∈ S`.
It is used with `S = X ∩ D` and `ρ = 1`. -/
def IsStronglyConvexWRT {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (Φ : E → ℝ) (Φ' : E → E →L[ℝ] ℝ) (ρ : ℝ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, Φ x - Φ y ≤ Φ' x (x - y) - ρ / 2 * ‖x - y‖ ^ 2

/-- `f` is `β`-smooth on `X` w.r.t. `‖·‖`, with gradient map `f'` (Ch. 4 preamble (ii), p. 297):
`f' x` is the derivative of `f` at `x` within `X` for every `x ∈ X`, and
`‖∇f(x) − ∇f(y)‖∗ ≤ β‖x − y‖` for all `x, y ∈ X`, the dual norm `‖·‖∗` being the operator norm
on `E →L[ℝ] ℝ`. -/
def IsSmoothWRT {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (f : E → ℝ) (f' : E → E →L[ℝ] ℝ) (β : ℝ) : Prop :=
  (∀ x ∈ X, HasFDerivWithinAt f (f' x) X x) ∧
    ∀ x ∈ X, ∀ y ∈ X, ‖f' x - f' y‖ ≤ β * ‖x - y‖

/-- `g` is a subgradient of `f` at `x` relative to `X` (Definition 1.2, p. 235, in the
arbitrary-norm convention): `f(x) − f(y) ≤ g⊤(x − y)` for every `y ∈ X`, with `g` a continuous
linear functional. -/
def IsSubgradientOnN {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (f : E → ℝ) (x : E) (g : E →L[ℝ] ℝ) : Prop :=
  ∀ y ∈ X, f x - f y ≤ g (x - y)

/-- A deterministic run of mirror descent in its argmin form (4.5) / the S-MD recursion of §6.1,
p. 330, with step `γ`, started at `x₁`, along the dual vectors `(g_s)_{s≥1}`:
`x₁ ∈ X ∩ D` minimizes `Φ` over `X ∩ D`, `x 1 = x₁`, and for every `s ≥ 1`, `x (s+1) ∈ X ∩ D`
minimizes `z ↦ γ g_s⊤z + D_Φ(z, x_s)` over `X ∩ D`. Index `0` is unused. -/
def IsMDArgminRun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X D : Set E) (Φ : E → ℝ) (Φ' : E → E →L[ℝ] ℝ) (γ : ℝ) (x₁ : E)
    (x : ℕ → E) (g : ℕ → E →L[ℝ] ℝ) : Prop :=
  (x₁ ∈ X ∩ D ∧ ∀ z ∈ X ∩ D, Φ x₁ ≤ Φ z) ∧ x 1 = x₁ ∧
    ∀ s : ℕ, 1 ≤ s →
      x (s + 1) ∈ X ∩ D ∧
        ∀ z ∈ X ∩ D,
          γ * g s (x (s + 1)) + bregman Φ Φ' (x (s + 1)) (x s) ≤ γ * g s z + bregman Φ Φ' z (x s)

/-- A run of stochastic mirror descent (S-MD), §6.1, p. 330, with step `γ`:
`x₁ ∈ argmin_{X ∩ D} Φ` (deterministic) and
`x_{s+1} ∈ argmin_{x ∈ X ∩ D} γ g̃(x_s)⊤x + D_Φ(x, x_s)`, realisation by realisation:
for every outcome `ω`, the sequence `s ↦ x s ω` is an argmin run (`IsMDArgminRun`) along the
oracle answers `s ↦ gt s ω` (`gt s` is `g̃(x_s)`, the oracle's answer at the query point `x_s`).
Its relation to `f` is carried by an oracle predicate (`IsSmoothStochOracle`,
`IsNonsmoothStochOracle`). -/
def IsSMDRun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Type*}
    (X D : Set E) (Φ : E → ℝ) (Φ' : E → E →L[ℝ] ℝ) (γ : ℝ) (x₁ : E)
    (x : ℕ → Ω → E) (gt : ℕ → Ω → E →L[ℝ] ℝ) : Prop :=
  ∀ ω, IsMDArgminRun X D Φ Φ' γ x₁ (fun s => x s ω) (fun s => gt s ω)

/-- The stochastic oracle of the smooth case (Ch. 6 preamble, pp. 329–330), along the query
points `x_s` (`s ≥ 1`), on the probability space `(Ω, μ)`: each query point `x_s` is a random
variable (measurable), the answer `g̃_s = gt s` is integrable, and, conditionally on the query
point (`E(· | x_s)` is the conditional expectation given `σ(x_s)`),
* unbiasedness: `E(g̃_s | x_s) = ∇f(x_s)` a.s. (for a differentiable `f`, `∂f(x) = {∇f(x)}`);
* variance bound: `E(‖g̃_s − ∇f(x_s)‖²∗ | x_s) ≤ σ²` a.s., with `‖g̃_s − ∇f(x_s)‖²∗` integrable. -/
def IsSmoothStochOracle {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f' : E → E →L[ℝ] ℝ) (σ : ℝ)
    (x : ℕ → Ω → E) (gt : ℕ → Ω → E →L[ℝ] ℝ) : Prop :=
  ∀ s : ℕ, 1 ≤ s →
    Measurable (x s) ∧ Integrable (gt s) μ ∧
      μ[gt s | MeasurableSpace.comap (x s) ‹MeasurableSpace E›] =ᵐ[μ] (fun ω => f' (x s ω)) ∧
      Integrable (fun ω => ‖gt s ω - f' (x s ω)‖ ^ 2) μ ∧
      μ[fun ω => ‖gt s ω - f' (x s ω)‖ ^ 2 | MeasurableSpace.comap (x s) ‹MeasurableSpace E›]
        ≤ᵐ[μ] (fun _ => σ ^ 2)

/-- The stochastic oracle of the non-smooth case (Ch. 6 preamble, pp. 329–330), along the query
points `x_s` (`s ≥ 1`): each query point is a random variable (measurable), the answer
`g̃_s = gt s` is integrable, and, conditionally on the query point,
* unbiasedness: `E(g̃_s | x_s) ∈ ∂f(x_s)` a.s. (a subgradient relative to `X`);
* second-moment bound: `E(‖g̃_s‖²∗ | x_s) ≤ B²` a.s., with `‖g̃_s‖²∗` integrable. -/
def IsNonsmoothStochOracle {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Set E) (f : E → ℝ) (B : ℝ)
    (x : ℕ → Ω → E) (gt : ℕ → Ω → E →L[ℝ] ℝ) : Prop :=
  ∀ s : ℕ, 1 ≤ s →
    Measurable (x s) ∧ Integrable (gt s) μ ∧
      (∀ᵐ ω ∂μ, IsSubgradientOnN X f (x s ω)
        ((μ[gt s | MeasurableSpace.comap (x s) ‹MeasurableSpace E›]) ω)) ∧
      Integrable (fun ω => ‖gt s ω‖ ^ 2) μ ∧
      μ[fun ω => ‖gt s ω‖ ^ 2 | MeasurableSpace.comap (x s) ‹MeasurableSpace E›]
        ≤ᵐ[μ] (fun _ => B ^ 2)

end ConvexOptAlg.StochMD
