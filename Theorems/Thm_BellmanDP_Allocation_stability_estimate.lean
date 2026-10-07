import Mathlib
import Definitions.Def_BellmanDP_Allocation_GeneralEquation

namespace BellmanDP.Allocation

/-- Ch. I, Theorem 9, p. 29. Let `u, v` be continuous on `x, y ≥ 0`, `0 < a, b < 1`,
`c = Max(a, b)`, `m(z) = Max_{0 ≤ x ≤ z} Max_{0 ≤ y ≤ x} Max(|u(x, y)|, |v(x, y)|)` with
`Σ m(cⁿ z) < ∞`, and `D(z) = Max_{0 ≤ x ≤ z} Max_{0 ≤ y ≤ x} |u(x, y) − v(x, y)|` with
`Σ D(cⁿ z) < ∞`, for all `z ≥ 0`. If `f` and `F` are continuous solutions on `x ≥ 0`, vanishing at
`0`, of `f(x) = Max_{0 ≤ y ≤ x} [u(x, y) + f(ay + b(x − y))]` and of the same equation with `v`,
then `|f(x) − F(x)| ≤ Σ_{n=0}^∞ D(cⁿ x)` for all `x ≥ 0`. -/
theorem stability_estimate (u v : ℝ → ℝ → ℝ) (a b : ℝ)
    (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) (hb1 : b < 1)
    (hu : ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ)))
    (hv : ContinuousOn (fun p : ℝ × ℝ => v p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ)))
    (hm : ∀ z : ℝ, 0 ≤ z → Summable (fun n : ℕ =>
      triangleMax (fun s t => max |u s t| |v s t|) (max a b ^ n * z)))
    (hD : ∀ z : ℝ, 0 ≤ z → Summable (fun n : ℕ =>
      triangleMax (fun s t => |u s t - v s t|) (max a b ^ n * z)))
    (f F : ℝ → ℝ)
    (hfc : ContinuousOn f (Set.Ici 0)) (hf0 : f 0 = 0) (hf : IsGeneralSolution u a b f)
    (hFc : ContinuousOn F (Set.Ici 0)) (hF0 : F 0 = 0) (hF : IsGeneralSolution v a b F) :
    ∀ x : ℝ, 0 ≤ x →
      |f x - F x| ≤ ∑' n : ℕ, triangleMax (fun s t => |u s t - v s t|) (max a b ^ n * x) := by sorry

end BellmanDP.Allocation

