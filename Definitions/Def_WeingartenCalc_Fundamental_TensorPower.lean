import Mathlib

namespace WeingartenCalc.Fundamental

open MeasureTheory Matrix

/-- Collins–Matsumoto–Novak, *The Weingarten Calculus*, arXiv:2109.14890v1, p. 3, (2):
the matrix of `U^{⊗d}(g)` in the product basis `e_i = e_{i(1)} ⊗ ⋯ ⊗ e_{i(d)}` of `H^{⊗d}`,
`U^{⊗d}_{ij}(g) = ∏_{x=1}^{d} U_{i(x) j(x)}(g)`, with `H = ℂ^N` and multi-indices
`i, j : Fin d → Fin N`. -/
def tensorPow {G : Type*} [Group G] {N : ℕ} (U : G →* Matrix.unitaryGroup (Fin N) ℂ) (d : ℕ)
    (g : G) : Matrix (Fin d → Fin N) (Fin d → Fin N) ℂ :=
  Matrix.of fun i j => ∏ x : Fin d, (U g : Matrix (Fin N) (Fin N) ℂ) (i x) (j x)

/-- p. 4: the space of `G`-invariant tensors
`(H^{⊗d})^G = {t ∈ H^{⊗d} : U^{⊗d}(g) t = t for all g ∈ G}`. -/
def invariants {G : Type*} [Group G] {N : ℕ} (U : G →* Matrix.unitaryGroup (Fin N) ℂ) (d : ℕ) :
    Submodule ℂ ((Fin d → Fin N) → ℂ) where
  carrier := {t | ∀ g : G, (tensorPow U d g).mulVec t = t}
  add_mem' := by
    intro s t hs ht g
    rw [Matrix.mulVec_add, hs g, ht g]
  zero_mem' := by
    intro g
    simp
  smul_mem' := by
    intro c t ht g
    rw [Matrix.mulVec_smul, ht g]

/-- p. 3: the averaging operator `P = ∫_G U^{⊗d}(g) dg`, the Bochner integral of the
matrix-valued function `g ↦ U^{⊗d}(g)` against `μ`. Matrices carry the entrywise sup norm
(`Matrix.normedAddCommGroup`) for this integral; in finite dimensions every norm gives the same
integral. -/
noncomputable def averagingOperator {G : Type*} [Group G] [MeasurableSpace G] (μ : Measure G)
    {N : ℕ} (U : G →* Matrix.unitaryGroup (Fin N) ℂ) (d : ℕ) :
    Matrix (Fin d → Fin N) (Fin d → Fin N) ℂ :=
  letI : NormedAddCommGroup (Matrix (Fin d → Fin N) (Fin d → Fin N) ℂ) :=
    Matrix.normedAddCommGroup
  letI : NormedSpace ℝ (Matrix (Fin d → Fin N) (Fin d → Fin N) ℂ) := Matrix.normedSpace
  ∫ g, tensorPow U d g ∂μ

/-- p. 4: the `N^d × m` matrix `A = [⟨e_i, a_x⟩]` whose columns are the coordinates of the
vectors `a_1, …, a_m`; with `H^{⊗d} = ℂ^{Fin d → Fin N}` and its standard basis,
`⟨e_i, a_x⟩ = a_x(i)`. -/
def coordMatrix {n : Type*} {m : ℕ} (a : Fin m → (n → ℂ)) : Matrix n (Fin m) ℂ :=
  Matrix.of fun i x => a x i

/-- p. 4: the Weingarten matrix `W = (A^* A)^{-1}`, the inverse of the Gram matrix
`A^* A = [⟨a_x, a_y⟩]` (Mathlib's `Matrix.inv`, which returns `0` on a singular matrix). -/
noncomputable def weingartenMatrix {n : Type*} [Fintype n] {m : ℕ} (a : Fin m → (n → ℂ)) :
    Matrix (Fin m) (Fin m) ℂ :=
  ((coordMatrix a)ᴴ * coordMatrix a)⁻¹

end WeingartenCalc.Fundamental
