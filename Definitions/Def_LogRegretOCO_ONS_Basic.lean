import Mathlib
open Matrix

namespace LogRegretOCO.ONS

/-- The quadratic form `vᵀ A v` of a real `n × n` matrix `A` at a point `v` of `ℝⁿ`
(Euclidean space; `WithLp.ofLp` reads off the coordinate vector). -/
noncomputable def quadForm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (v : EuclideanSpace ℝ (Fin n)) : ℝ :=
  WithLp.ofLp v ⬝ᵥ (A *ᵥ WithLp.ofLp v)

/-- Generalized projection (Hazan–Agarwal–Kale 2007, Fig. 2 and §4, p. 188):
`z` is *a* generalized projection of `y` onto `P` with respect to `A`, i.e. `z ∈ P` and `z`
minimises `(y − x)ᵀ A (y − x)` over `x ∈ P`. Every minimiser qualifies (any tie-break). -/
def IsGenProj {n : ℕ} (P : Set (EuclideanSpace ℝ (Fin n))) (A : Matrix (Fin n) (Fin n) ℝ)
    (y z : EuclideanSpace ℝ (Fin n)) : Prop :=
  z ∈ P ∧ ∀ w ∈ P, quadForm A (y - z) ≤ quadForm A (y - w)

/-- The regularised Gram matrix `V_t = Σ_{τ=1}^t u_τ u_τᵀ + ε Iₙ` of a sequence of vectors
(rounds are 1-based; `u 0` is never used). -/
noncomputable def regGram {n : ℕ} (ε : ℝ) (u : ℕ → EuclideanSpace ℝ (Fin n)) (t : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  ∑ τ ∈ Finset.Icc 1 t, Matrix.vecMulVec (WithLp.ofLp (u τ)) (WithLp.ofLp (u τ)) +
    ε • (1 : Matrix (Fin n) (Fin n) ℝ)

end LogRegretOCO.ONS
