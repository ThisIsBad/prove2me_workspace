import Mathlib

namespace SupportVectorMachines.InfiniteSample

/-- `H` (with evaluation map `toFun : H →ₗ[ℝ] (X → ℝ)`, realizing `H` concretely as a Hilbert
space of functions on `X`, Definition 4.18, p. 118, restated locally per Hard Rule 9) **is the
RKHS of the kernel `k`** if `toFun` is injective (distinct elements of `H` are distinct
functions, i.e. `H` genuinely "consists of functions", Definition 4.18's standing hypothesis) and
`k` is a reproducing kernel of `H` (Definition 4.18(i)): for every `x`, the function `k(·,x)` lies
in `H` (via some `kAt x : H` with `toFun (kAt x) = k(·,x)`), and the reproducing property
`f(x) = ⟨f, k(·,x)⟩` holds for every `f ∈ H` and `x ∈ X`. By Lemma 4.19, a Hilbert function space
with a reproducing kernel is automatically an RKHS (Definition 4.18(ii): every Dirac functional
`f ↦ f(x)` is continuous, via Cauchy-Schwarz applied to the reproducing property), so this
reproducing-kernel formulation is an equivalent, operative rendering of "`H` is an RKHS with
kernel `k`" — the form Theorem 5.5 and its neighbors actually use. -/
def IsRKHSOfKernel {X : Type*} (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (toFun : H →ₗ[ℝ] (X → ℝ)) (k : X → X → ℝ) : Prop :=
  Function.Injective toFun ∧
    ∃ kAt : X → H, (∀ x x' : X, toFun (kAt x) x' = k x x') ∧
      ∀ (f : H) (x : X), toFun f x = inner (𝕜 := ℝ) f (kAt x)

end SupportVectorMachines.InfiniteSample
