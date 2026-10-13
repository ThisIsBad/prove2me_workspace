import Mathlib
import Definitions.Def_SendSplit_Existence_Network

namespace SendSplit.Existence

theorem concave_sandwich {n : ℕ} (G : ArcGraph n) (c : Fin n → Fin n → ℝ → ℝ)
    (hc : IsConcaveArcCost G c) (x y : Fin n → Fin n → ℝ) (hx : IsPreflow G x)
    (hy : IsPreflow G y) (θ : ℝ) (hθ : 0 ≤ θ) :
    (1 / 2 : ℝ) * flowCost G c (fun i j => 2 * x i j)
        + (1 / 2 : ℝ) * flowCost G c (fun i j => 2 * (θ * y i j))
        ≤ flowCost G c (fun i j => x i j + θ * y i j) ∧
      flowCost G c (fun i j => x i j + θ * y i j)
        ≤ flowCost G c x + flowCost G c (fun i j => θ * y i j) := by sorry

end SendSplit.Existence

