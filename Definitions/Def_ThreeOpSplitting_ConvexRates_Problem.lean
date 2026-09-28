import Mathlib

open InnerProductSpace

namespace ThreeOpSplitting.ConvexRates

/-- `f : H → (-∞, +∞]` is closed, proper and convex: it never takes the value `-∞`, it is finite
somewhere, it is lower semicontinuous (closed), and its epigraph `{(x, t) | f x ≤ t}` is convex. -/
def IsProperClosedConvex {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → EReal) : Prop :=
  (∀ x : H, f x ≠ ⊥) ∧ (∃ x : H, f x ≠ ⊤) ∧ LowerSemicontinuous f ∧
    Convex ℝ {p : H × ℝ | f p.1 ≤ (p.2 : EReal)}

/-- `P` is (a choice of) the proximal map `prox_{γf}`: for every `x`, `P x` minimises
`y ↦ f y + ‖y - x‖² / (2γ)`. For `f` closed, proper, convex and `γ > 0` the minimiser exists and
is unique, so `P` is then determined. -/
def IsProx {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (γ : ℝ) (f : H → EReal) (P : H → H) : Prop :=
  ∀ x y : H, f (P x) + ((‖P x - x‖ ^ 2 / (2 * γ) : ℝ) : EReal) ≤
    f y + ((‖y - x‖ ^ 2 / (2 * γ) : ℝ) : EReal)

/-- `h : H → ℝ` is convex and differentiable and its gradient `∇h` is `β⁻¹`-Lipschitz. -/
def IsSmoothConvex {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (β : ℝ) (h : H → ℝ) : Prop :=
  ConvexOn ℝ Set.univ h ∧ Differentiable ℝ h ∧
    ∀ x y : H, ‖gradient h x - gradient h y‖ ≤ β⁻¹ * ‖x - y‖

/-- The objective `(f + g + h)(x)` of problem (3.1), valued in `(-∞, +∞]`. -/
noncomputable def objective {H : Type*} (f g : H → EReal) (h : H → ℝ) (x : H) : EReal :=
  f x + g x + (h x : EReal)

end ThreeOpSplitting.ConvexRates
