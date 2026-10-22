import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
import Definitions.Def_NonsmoothNewton_Local_dirDeriv
import Definitions.Def_NonsmoothNewton_Local_SemismoothAt
import Definitions.Def_QiNonsmoothEq_Local_Setting
open Filter Topology

namespace QiNonsmoothEq.Local

/-- Qi (1993), Theorem 3.1 (Local Convergence), first paragraph, p. 234. Let `x*` be a zero of
`F`, and let `F` be semismooth and strongly BD-regular at `x*`. Then there is `δ > 0` such that:
(1) for every `y` with `‖y - x*‖ < δ`, every `V ∈ ∂_B F(y)` is nonsingular and the Newton point
`y - V⁻¹F(y)` is again within `δ` of `x*` (the method (3.2) is well defined);
(2) every run of (3.2), `x^{k+1} = x^k - V_k⁻¹F(x^k)` with `V_k ∈ ∂_B F(x^k)` arbitrary, started
with `‖x^0 - x*‖ < δ`, has every `V_k` nonsingular, converges to `x*`, and superlinearly:
`‖x^{k+1} - x*‖ = o(‖x^k - x*‖)`;
(3) if moreover `F(x^k) ≠ 0` for all `k`, then `‖F(x^{k+1})‖ / ‖F(x^k)‖ → 0` (1.9). -/
theorem theorem_3_1 {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hF : LocallyLipschitz F) (xstar : EuclideanSpace ℝ (Fin n)) (hzero : F xstar = 0)
    (hss : NonsmoothNewton.Local.SemismoothAt F xstar) (hreg : StronglyBDRegularAt F xstar) :
    ∃ δ > 0,
      (∀ y : EuclideanSpace ℝ (Fin n), ‖y - xstar‖ < δ →
        ∀ V ∈ NonsmoothNewton.Shared.bJac F y,
          (∃ W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n), IsInverse V W) ∧
          ∀ W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n), IsInverse V W →
            ‖y - W (F y) - xstar‖ < δ) ∧
      (∀ (x : ℕ → EuclideanSpace ℝ (Fin n))
          (V : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)),
        IsBDNewtonRun F x V → ‖x 0 - xstar‖ < δ →
          (∀ k, ∃ W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n),
            IsInverse (V k) W) ∧
          Tendsto x atTop (𝓝 xstar) ∧
          (fun k => x (k + 1) - xstar) =o[atTop] (fun k => x k - xstar) ∧
          ((∀ k, F (x k) ≠ 0) →
            Tendsto (fun k => ‖F (x (k + 1))‖ / ‖F (x k)‖) atTop (𝓝 0))) := by sorry

end QiNonsmoothEq.Local

