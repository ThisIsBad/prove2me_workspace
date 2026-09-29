import Mathlib
import Definitions.Def_FatkhullinPolyak_Discrete_LQR

open Filter Topology

namespace FatkhullinPolyak.Discrete

/-- Lemma C.2 (p. 18): for `K ∈ S` and `Y` the solution of `A_K Y + Y A_Kᵀ + Σ = 0`,
(C.7) `λₙ(Y) ≤ f(K) / λ₁(Q + CᵀKᵀRKC)`. -/
theorem lyapY_eigen_upper {n m r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (Sig : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q.PosDef) (hR : R.PosDef) (hSig : Sig.PosDef) (hC : C.rank = r) (hB : B ≠ 0)
    (K : Matrix (Fin m) (Fin r) ℝ) (hK : K ∈ stabSet A B C) :
    lamMax (lyapY A B C Sig K) ≤
      lqrCost A B C Q R Sig K / lamMin (Q + C.transpose * K.transpose * R * K * C) := by sorry

end FatkhullinPolyak.Discrete
