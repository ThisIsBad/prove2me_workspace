import Mathlib
import Definitions.Def_FatkhullinPolyak_Discrete_LQR

open Filter Topology

namespace FatkhullinPolyak.Discrete

/-- Lemma 3.11 (p. 7): for every `K ∈ S`, `f` is Fréchet differentiable at `K` (Frobenius norm)
with gradient `∇f(K) = 2(RKC − BᵀX)YCᵀ` of (3.3), `Y` the solution of (3.4); i.e.
`f(K + E) = f(K) + ⟨∇f(K), E⟩_F + o(‖E‖_F)`. -/
theorem lqr_gradient_formula {n m r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (Sig : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q.PosDef) (hR : R.PosDef) (hSig : Sig.PosDef) (hC : C.rank = r) (hB : B ≠ 0)
    (K : Matrix (Fin m) (Fin r) ℝ) (hK : K ∈ stabSet A B C) :
    ∀ ε > 0, ∃ δ > 0, ∀ E : Matrix (Fin m) (Fin r) ℝ, frobNorm E < δ →
      |lqrCost A B C Q R Sig (K + E) - lqrCost A B C Q R Sig K
          - frobInner (lqrGrad A B C Q R Sig K) E| ≤ ε * frobNorm E := by sorry

end FatkhullinPolyak.Discrete
