import Mathlib
import Definitions.Def_FatkhullinPolyak_Discrete_LQR

open Filter Topology

namespace FatkhullinPolyak.Discrete

/-- Lemma 3.8 (p. 7): `f` is coercive on `S` (continuous on `S`, and `f(Kⱼ) → +∞` along any
sequence in `S` with `‖Kⱼ‖ → ∞` or `Kⱼ → K ∈ ∂S`), and for every `K ∈ S`
(3.1) `f(K) ≥ λ₁(Σ)λ₁(Q) / (−2ℜλₙ(A_K))`,
(3.2) `f(K) ≥ λ₁(Σ)λ₁(R)‖K‖_F² λ₁(CCᵀ) / (2‖A‖ + 2‖K‖_F‖B‖‖C‖)`. -/
theorem lqrCost_coercive_bounds {n m r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (Sig : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q.PosDef) (hR : R.PosDef) (hSig : Sig.PosDef) (hC : C.rank = r) (hB : B ≠ 0) :
    ContinuousOn (lqrCost A B C Q R Sig) (stabSet A B C) ∧
    (∀ Ks : ℕ → Matrix (Fin m) (Fin r) ℝ, (∀ j, Ks j ∈ stabSet A B C) →
      Tendsto (fun j => frobNorm (Ks j)) atTop atTop →
      Tendsto (fun j => lqrCost A B C Q R Sig (Ks j)) atTop atTop) ∧
    (∀ (Ks : ℕ → Matrix (Fin m) (Fin r) ℝ) (K : Matrix (Fin m) (Fin r) ℝ),
      (∀ j, Ks j ∈ stabSet A B C) → K ∈ frontier (stabSet A B C) →
      Tendsto Ks atTop (𝓝 K) →
      Tendsto (fun j => lqrCost A B C Q R Sig (Ks j)) atTop atTop) ∧
    (∀ K ∈ stabSet A B C,
      lamMin Sig * lamMin Q / (-2 * maxRe (A - B * K * C)) ≤ lqrCost A B C Q R Sig K ∧
      lamMin Sig * lamMin R * frobNorm K ^ 2 * lamMin (C * C.transpose) /
          (2 * specNorm A + 2 * frobNorm K * specNorm B * specNorm C)
        ≤ lqrCost A B C Q R Sig K) := by sorry

end FatkhullinPolyak.Discrete
