import Mathlib
import Definitions.Def_FatkhullinPolyak_Discrete_LQR

open Filter Topology

namespace FatkhullinPolyak.Discrete

/-- Lemma C.3 (p. 18), state feedback `C = I`: for `K ∈ S`,
(C.8) `‖K‖_F ≤ 2‖B‖f(K) / (λ₁(Σ)λ₁(R)) + ‖A‖/‖B‖`. -/
theorem slqr_gain_norm_bound {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (Sig : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q.PosDef) (hR : R.PosDef) (hSig : Sig.PosDef) (hB : B ≠ 0)
    (K : Matrix (Fin m) (Fin n) ℝ) (hK : K ∈ stabSet A B (1 : Matrix (Fin n) (Fin n) ℝ)) :
    frobNorm K ≤ 2 * specNorm B * lqrCost A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K / (lamMin Sig * lamMin R)
      + specNorm A / specNorm B := by sorry

end FatkhullinPolyak.Discrete
