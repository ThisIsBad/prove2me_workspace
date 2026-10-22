import Mathlib

namespace RobinsonSR.IFT

open scoped Topology

/-- The normal-cone operator `∂ψ_C` (Robinson 1980, §1, p. 43): for `x ∈ C` it is the set of
continuous linear functionals `y ∈ X′` with `y (c - x) ≤ 0` for all `c ∈ C`; for `x ∉ C` it is `∅`. -/
def normalCone {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (C : Set X) (x : X) : Set (StrongDual ℝ X) :=
  {y | x ∈ C ∧ ∀ c ∈ C, y (c - x) ≤ 0}

/-- Strong regularity (DEFINITION, p. 45), stated on the data of the linearisation:
`a` plays `f(x₀)` and `A` plays `f′(x₀)`, so that `T x = a + A (x - x₀) + ∂ψ_C(x)`.
The generalized equation is strongly regular at `x₀` with associated Lipschitz constant `lam`
if there are neighbourhoods `U` of `0` in `X′` and `V` of `x₀` such that the restriction to `U`
of `T⁻¹ ∩ V` is a single-valued function `s : U → V` that is Lipschitzian on `U` with modulus
`lam`: for each `y ∈ U`, `s y ∈ V` solves `y ∈ T (s y)`, it is the only solution in `V`, and
`‖s y₁ - s y₂‖ ≤ lam * ‖y₁ - y₂‖` on `U`. -/
def StronglyRegular {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (C : Set X) (a : StrongDual ℝ X) (A : X →L[ℝ] StrongDual ℝ X) (x0 : X) (lam : ℝ) : Prop :=
  ∃ U ∈ 𝓝 (0 : StrongDual ℝ X), ∃ V ∈ 𝓝 x0, ∃ s : StrongDual ℝ X → X,
    (∀ y ∈ U, s y ∈ V ∧ y - (a + A (s y - x0)) ∈ normalCone C (s y) ∧
       ∀ x ∈ V, y - (a + A (x - x0)) ∈ normalCone C x → x = s y) ∧
    ∀ y₁ ∈ U, ∀ y₂ ∈ U, ‖s y₁ - s y₂‖ ≤ lam * ‖y₁ - y₂‖

/-- The residual of the proof of Theorem 2.1 (p. 45):
`r(p, x) = f(p₀, x₀) + f′(p₀, x₀)(x − x₀) − f(p, x)`, where `f′` is the partial Fréchet derivative
of `f` in its second variable. -/
noncomputable def residual {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {P : Type*}
    (f : P → X → StrongDual ℝ X) (f' : P → X → (X →L[ℝ] StrongDual ℝ X)) (p0 : P) (x0 : X)
    (p : P) (x : X) : StrongDual ℝ X :=
  f p0 x0 + f' p0 x0 (x - x0) - f p x

end RobinsonSR.IFT
