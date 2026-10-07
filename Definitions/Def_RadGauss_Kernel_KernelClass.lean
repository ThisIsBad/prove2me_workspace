import Mathlib

namespace RadGauss.Kernel

/-- **Kernel** (Bartlett–Mendelson 2002, §4.3, p. 476): a kernel `k : 𝒳 × 𝒳 → ℝ` on a compact
space `𝒳` is a continuous function such that for every `m` and all `x_1, …, x_m ∈ 𝒳` the Gram
matrix `K_ij = k(x_i, x_j)` is symmetric and positive semidefinite. `k` is written curried;
continuity is joint continuity of `(x, y) ↦ k x y`. Mathlib's `Matrix.PosSemidef` of a real
matrix includes symmetry (`IsHermitian`). -/
structure IsKernel {X : Type*} [TopologicalSpace X] (k : X → X → ℝ) : Prop where
  compactSpace : CompactSpace X
  continuous : Continuous (Function.uncurry k)
  gram_posSemidef : ∀ (m : ℕ) (x : Fin m → X), (Matrix.of fun i j => k (x i) (x j)).PosSemidef

/-- **The class of kernel expansions** (§4.3, p. 477):
`F = {x ↦ Σ_{i=1}^m α_i k(x, x_i) : m ∈ ℕ, x_i ∈ 𝒳, Σ_{i,j} α_i α_j k(x_i, x_j) ≤ B²}`,
every finite expansion with centres `c_1, …, c_m` anywhere in `𝒳` (repetitions allowed, `m = 0`
gives the zero function) and real coefficients `α` with `α'Kα ≤ B²`. -/
def kernelClass {X : Type*} (k : X → X → ℝ) (B : ℝ) : Set (X → ℝ) :=
  {f | ∃ (m : ℕ) (c : Fin m → X) (α : Fin m → ℝ),
    ∑ i, ∑ j, α i * α j * k (c i) (c j) ≤ B ^ 2 ∧ f = fun x => ∑ i, α i * k x (c i)}

end RadGauss.Kernel
